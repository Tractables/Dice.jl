using MacroTools: prewalk, postwalk
using IRTools
using IRTools: @dynamo, IR, recurse!, self, xcall, functional

export @dice_ite, @dice, dice, observe, observation

##################################
# Control flow macro
##################################

"Syntactic macro to make if-then-else supported by dice"
macro dice_ite(code)
    postwalk(esc(code)) do x
        if x isa Expr && (x.head == :if || x.head == :elseif)
            @assert length(x.args) == 3 "@dice_ite macro only supports purely functional if-then-else"
            ite_guard = gensym(:ite)
            return :(begin $ite_guard = $(x.args[1])
                    if ($(ite_guard) isa Dist{Bool})
                        Dice.ifelse($(ite_guard), $(x.args[2:3]...))
                    else
                        (if $(ite_guard)
                            $(x.args[2])
                        else
                            $(x.args[3])
                        end)
                    end
                end)
        end
        return x
    end
end

##################################
# Control flow + error + observation dynamo
##################################

"A distribution computed by a dice program with metadata on observes and errors"
struct MetaDist
    dist::Dist
    errors::Vector{Tuple{AnyBool, String}}
    observations::Vector{AnyBool}
end

observation(x) = reduce(&, x.observations; init=true)

"Interpret dice code with control flow, observations, and errors"
function dice(f) 
    dyna = DiceDyna()
    x = dyna(f)
    MetaDist(x, dyna.errors, dyna.observations)
end

"Interpret dice code with control flow, observations, and errors"
macro dice(code)
    esc(quote
        dice() do #, __dsl_errors__[], __dsl_observation__[]
            $code
        end
    end)
end


struct DiceDyna
    path::Vector{AnyBool}
    errors::Vector{Tuple{AnyBool, String}}
    observations::Vector{AnyBool}
    DiceDyna() = new(AnyBool[], Tuple{AnyBool, String}[], AnyBool[])
end

"Assert that the current code must be run within an @dice evaluation"
assert_dice() = error("This code must be called from within an @dice evaluation.")

observe(_) = assert_dice()

@dynamo function (dyna::DiceDyna)(a...)
    ir = IR(a...)
    (ir === nothing) && return
    ir = functional(ir)
    ir = prewalk(ir) do x
        if x isa Expr && x.head == :call
            return xcall(self, x.args...)
        end
        return x
    end
    return ir
end

(::DiceDyna)(::typeof(assert_dice)) = nothing

(::DiceDyna)(::typeof(IRTools.cond), guard, then, elze) = IRTools.cond(guard, then, elze)

function (dyna::DiceDyna)(::typeof(IRTools.cond), guard::Dist{Bool}, then, elze)
    push!(dyna.path, guard)
    t = then()
    pop!(dyna.path)
    push!(dyna.path, !guard)
    e = elze()
    pop!(dyna.path)
    ifelse(guard, t, e)
end

path_condition(dyna) = reduce(&, dyna.path; init=true)

(dyna::DiceDyna)(::typeof(error), msg) =
    push!(dyna.errors, (path_condition(dyna), msg))

(dyna::DiceDyna)(::typeof(observe), x) =
    push!(dyna.observations, !path_condition(dyna) | x)

# avoid transformation when it is known to trigger a bug
for f in :[getfield, typeof, Core.apply_type, typeassert, (===), ifelse,
        Core.sizeof, Core.arrayset, tuple, isdefined, fieldtype, nfields,
        isa, Core.arraysize, repr, print, println, Base.vect, Broadcast.broadcasted,
        Broadcast.materialize, Core.Compiler.return_type, Base.union!, Base.getindex, Base.haskey,
        Base.pop!, Base.setdiff, unsafe_copyto!].args
    @eval (::DiceDyna)(::typeof($f), args...) = $f(args...)
end