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
