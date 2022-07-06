export pr, Cudd

abstract type InferAlgo end
struct Cudd <: InferAlgo end

"Compute probability of a Dice.jl program"
pr(x::Bool) = x ? 1.0 : 0.0
pr(x::Dist) = pr(x, Cudd())

function pr(x::MetaDist)
    @assert isempty(x.errors) "TODO"
    
    evidence = observation(x)
    numerator = pr(x.dist & evidence)
    denominator = pr(evidence) 

    numerator/denominator
end

include("cudd.jl")