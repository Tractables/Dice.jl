using MacroTools: postwalk, @capture
using IRTools
using IRTools: @dynamo, IR, recurse!, self

export @dice_ite, @dice, dice

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

"A distribution computed by a dice program with metadata on observes and errors"
struct MetaDist
    dist::Dist
    obs
    err
end

"Assert that the current code must be run within an @dice evaluation"
assert_dice() = error("This code must be called from within an @dice evaluation.")

dice(::typeof(assert_dice)) = nothing

@dynamo function dice(a...)
    ir = IR(a...)
    (ir === nothing) && return
    recurse!(ir, dice)
    return IRTools.functional(ir)
end

# avoid transformation when it is known to trigger a bug
for f in :[getfield, typeof, Core.apply_type, typeassert, (===), ifelse,
        Core.sizeof, Core.arrayset, tuple, isdefined, fieldtype, nfields,
        isa, Core.arraysize, repr, print, println, Base.vect, Broadcast.broadcasted,
        Broadcast.materialize, Core.Compiler.return_type, Base.union!, Base.getindex, Base.haskey,
        Base.pop!, Base.setdiff, unsafe_copyto!].args
    @eval dice(::typeof($f), args...) = $f(args...)
end

# __dsl_path__ = Ref{Any}(nothing)
# __dsl_errors__ = Ref{Any}(nothing)
# __dsl_observation__ = Ref{Any}(nothing)
# __dsl_code__ = Ref{Any}(nothing)
macro dice(code)
    esc(quote
#         __dsl_path__[] = DistBool[DistTrue()]
#         __dsl_errors__[] = Tuple{DistBool, String}[(DistFalse(), "dummy")]
#         __dsl_observation__[] = DistTrue()
        dice() do #, __dsl_errors__[], __dsl_observation__[]
            $code
        end
    end)
end

# #############################################
# # add path conditions
# #############################################


IRTools.cond(guard::Dist{Bool}, then, elze) = ifelse(guard, then(), elze())

# function IRTools.cond(guard::DistBool, then, elze)
#     push!(__dsl_path__[], guard)
#     t = then()
#     pop!(__dsl_path__[])
#     push!(__dsl_path__[], !guard)
#     e = elze()
#     pop!(__dsl_path__[])
#     ifelse(guard, t, e)
# end

# function prob_error(msg)
#     push!(__dsl_errors__[], (reduce(&, __dsl_path__[]), msg))
#     nothing
# end

# function observe(x)
#     __dsl_observation__[] &= !reduce(&, __dsl_path__[]) | x
#     nothing
# end
