export pr, Cudd

abstract type InferAlgo end
struct Cudd <: InferAlgo end

"Compute probability of a Dice.jl program"
pr(x::Bool) = x ? 1.0 : 0.0
pr(x::Dist) = pr(x, Cudd())

function pr(x::MetaDist)
    @assert isempty(x.errors) "TODO"
    @assert isempty(x.observations) "TODO"
    pr(x.dist)
end

include("cudd.jl")