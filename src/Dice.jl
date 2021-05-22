module Dice

__precompile__(false) # until https://github.com/sisl/CUDD.jl/issues/15 is fixed

include("language.jl")
include("parser.jl")
include("prob_data.jl")
include("compiler.jl")
include("backend.jl")

end # module
