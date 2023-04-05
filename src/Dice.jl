module Dice

##################################
# Control flow macro
##################################

using MacroTools: prewalk, postwalk

export @dice_ite

"Syntactic macro to make if-then-else supported by dice"
macro dice_ite(code)
    postwalk(esc(code)) do x
        if x isa Expr && (x.head == :if || x.head == :elseif)
            @assert length(x.args) == 3 "@dice_ite macro only supports purely functional if-then-else"
            ite_guard = gensym(:ite)
            return :(begin $ite_guard = $(x.args[1])
                    if (!Dice.indynamo() && ($(ite_guard) isa Dist{Bool} || $(ite_guard) isa Cond{<:Dist{Bool}}))
                        ifelse($(ite_guard), $(x.args[2:3]...))
                    else
                        $(ite_guard) isa Cond{Bool} && ($(ite_guard) = $(ite_guard).x)
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

include("monad.jl")
include("dist/dist.jl")
include("inference/inference.jl")
include("analysis/analysis.jl")
include("dsl.jl")
include("plot.jl")
include("util.jl")

end # module
