using MacroTools: postwalk
export @dice_ite

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
                        ifelse($(ite_guard), $(x.args[2:3]...))
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