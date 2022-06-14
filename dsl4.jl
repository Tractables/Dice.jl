using Dice
using IfElse: ifelse

# TODO turn into a unit test later

#############################################
# dynamo to construct a weighted boolean formula
#############################################

using IRTools
using IRTools: @dynamo, IR, recurse!, self

# pirate `IRTools.cond`` but keep default behavior on Bool guards
IRTools.cond(guard::Bool, then, elze) = guard ? then() : elze()
IRTools.cond(guard, then, elze) = ifelse(guard, then(), elze())

@dynamo function dice_formula(a...)
    ir = IR(a...)
    (ir === nothing) && return
    recurse!(ir, dice_formula)
    return IRTools.functional(ir)
end

# avoid transformation when it is known to trigger a bug
dice_formula(::typeof(unsafe_copyto!), args...) = unsafe_copyto!(args...)

foo(x) = flip(x) ? flip(x/2) : flip(x/4)

dice_formula() do 
    foo(0.9)
end

#############################################
# add path conditions
#############################################

# because dynamos with context don't work currently with lambdas, we use global state for now

const path = DistBool[]
const errors = []

function IRTools.cond(guard::DistBool, then, elze) 
    push!(path, guard)
    t = then()
    pop!(path)
    push!(path, !guard)
    e = elze()
    pop!(path)
    ifelse(guard, t, e)
end

function error(msg) 
    push!(errors, (reduce(&, path), msg))
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

dice_formula() do 
    finite_quotient(foo(0.5), foo(0.5))
end

errors