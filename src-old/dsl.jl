using MacroTools: postwalk, @capture
using IRTools
using IRTools: @dynamo, IR, recurse!, self

export @dice, @dice_ite, observe, prob_error, dice_formula, require_dice_transformation, __dsl_path__, __dsl_errors__, __dsl_observation__, __dsl_code__

macro dice_ite(code)
    postwalk(esc(code)) do x
        # TODO: replace by custom desugaring that is still lazy for boolean guards
        # this will not work in general
        # for example when control flow has `return`` inside
        if x isa Expr && (x.head == :if || x.head == :elseif)
            @assert length(x.args) == 3 "@dice_ite macro only supports purely functional if-then-else"
            # return :($ite($(x.args...)))
            ite_guard = gensym(:ite)
            return :(begin $ite_guard = $(x.args[1])
                    if ($(ite_guard) isa DistBool || $(ite_guard) isa Dice.DWE)
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

#############################################
# dynamo to construct a weighted boolean formula
#############################################

# pirate `IRTools.cond`` but keep default behavior on Bool guards
IRTools.cond(guard::Bool, then, elze) = guard ? then() : elze()
IRTools.cond(guard, then, elze) = ifelse(guard, then(), elze())

require_dice_transformation() = error("This must be called from within @dice!")
dice_formula(::typeof(require_dice_transformation)) = nothing

@dynamo function dice_formula(a...)
    ir = IR(a...)
    (ir === nothing) && return
    recurse!(ir, dice_formula)
    return IRTools.functional(ir)
end

# avoid transformation when it is known to trigger a bug
for f in :[getfield, typeof, Core.apply_type, typeassert, (===), ifelse,
        Core.sizeof, Core.arrayset, tuple, isdefined, fieldtype, nfields,
        isa, Core.arraysize, repr, print, println, Base.vect, Broadcast.broadcasted,
        Broadcast.materialize, Core.Compiler.return_type, Base.union!, Base.getindex, Base.haskey,
        Base.pop!, Base.setdiff, unsafe_copyto!].args
    @eval dice_formula(::typeof($f), args...) = $f(args...)
end

__dsl_path__ = Ref{Any}(nothing)
__dsl_errors__ = Ref{Any}(nothing)
__dsl_observation__ = Ref{Any}(nothing)
__dsl_code__ = Ref{Any}(nothing)
macro dice(code)
    esc(quote
        __dsl_path__[] = DistBool[DistTrue()]
        __dsl_errors__[] = Tuple{DistBool, String}[(DistFalse(), "dummy")]
        __dsl_observation__[] = DistTrue()
        __dsl_code__[] = () -> $code
        dice_formula(__dsl_code__[]), __dsl_errors__[], __dsl_observation__[]
    end)
end

#############################################
# add path conditions
#############################################

function IRTools.cond(guard::DistBool, then, elze)
    push!(__dsl_path__[], guard)
    t = then()
    pop!(__dsl_path__[])
    push!(__dsl_path__[], !guard)
    e = elze()
    pop!(__dsl_path__[])
    ifelse(guard, t, e)
end

function prob_error(msg)
    push!(__dsl_errors__[], (reduce(&, __dsl_path__[]), msg))
    nothing
end

function observe(x)
    __dsl_observation__[] &= !reduce(&, __dsl_path__[]) | x
    nothing
end
