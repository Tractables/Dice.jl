using Dice
using IfElse: ifelse

# TODO turn into a unit test later

#############################################
# dynamo to construct a weighted boolean formula
#############################################

using IRTools
using IRTools: @dynamo, IR, recurse!, self

path_sym = gensym("path")
errors_sym = gensym("errors")
observation_sym = gensym("observation")
code_sym = gensym("code")

# pirate `IRTools.cond`` but keep default behavior on Bool guards
IRTools.cond(guard::Bool, then, elze) = guard ? then() : elze()
IRTools.cond(guard, then, elze) = ifelse(guard, then(), elze())

macro dice(code)
    esc(quote
        global $path_sym = DistBool[DistTrue()]
        global $errors_sym = Tuple{DistBool, String}[(DistFalse(), "dummy")]
        global $observation_sym = DistTrue()
        global $code_sym = () -> $code
        dice_formula($code_sym), $errors_sym, $observation_sym
    end)
end

@dynamo function dice_formula(a...)
    ir = IR(a...)
    (ir === nothing) && return
    recurse!(ir, dice_formula)
    return IRTools.functional(ir)
end

# avoid transformation when it is known to trigger a bug
dice_formula(::typeof(unsafe_copyto!), args...) = unsafe_copyto!(args...)

foo(x) = flip(x) ? flip(x/2) : flip(x/4)

@dice begin 
    foo(0.9)
end

#############################################
# add path conditions
#############################################

function IRTools.cond(guard::DistBool, then, elze)
    path = eval(path_sym)
    push!(path, guard)
    t = then()
    pop!(path)
    push!(path, !guard)
    e = elze()
    pop!(path)
    ifelse(guard, t, e)
end

function error(msg)
    path = eval(path_sym)
    errors = eval(errors_sym)
    push!(errors, (reduce(&, path), msg))
    nothing
end

function observe(x)
    path = eval(path_sym)
    observation = eval(observation_sym)
    global observation &= !reduce(&, path) | x
    nothing
end

function finite_quotient(x,y)
   if !x && !y
        error("0/0 is undefined")
        false
   elseif x && !y 
        false
   else
        true
   end
end

quo, errors, observation = @dice begin
    finite_quotient(flip(0.5), flip(0.5))
end
total_error = reduce(|, [err for (err, msg) in errors])
dist, error_p = infer(DWE(quo, total_error))

d, errors, observation = @dice begin
    flipA = flip(0.3)
    flipB = flip(0.5)
    observe(flipA)
    !prob_equals(flipA, flipB)
end

dist = infer_with_observation(d, observation)