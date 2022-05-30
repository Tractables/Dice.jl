using MacroTools: postwalk, @capture

export @dice, compile, rundice

struct DiceCode
    interpret::Function
end

"""
process dice code before running it
currently it makes if-then-else, &&, and || polymorphic
"""
function to_dice(code)

    # manual hygiene
    mgr = gensym(:mgr)
    ite = gensym(:ite)
    ite_guard = gensym(:ite)

    transformed_code = postwalk(esc(code)) do x
        # TODO: replace by custom desugaring that is still lazy for boolean guards
        # this will not work in general
        # for example when control flow has `return`` inside
        if x isa Expr && (x.head == :if || x.head == :elseif)
            @assert length(x.args) == 3 "@dice macro only supports purely functional if-then-else"
            # return :($ite($(x.args...)))
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
        @capture(x, A_ || B_) && return :($A | $B) 
        @capture(x, A_ && B_) && return :($A & $B) 
        return x
    end

    return transformed_code
end

macro dice(code)
    to_dice(code)
end
