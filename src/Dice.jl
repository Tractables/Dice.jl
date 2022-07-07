module Dice

"A choice of probabilistic inference algorithm"
abstract type InferAlgo end

include("dist/dist.jl")
include("inference/inference.jl")
include("dsl.jl")

end # module
