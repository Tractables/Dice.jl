export pr, Cudd

abstract type InferAlgo end
struct Cudd <: InferAlgo end

"Compute probability of `Dist`, using `Cudd` as default inference algorithm"
pr(x::Dist) = pr(x, Cudd())

include("cudd.jl")