export pr, condpr, Cudd, ProbException

abstract type InferAlgo end
struct Cudd <: InferAlgo end

"Compute probability of a Dice.jl program"
pr(x::Bool) = x ? 1.0 : 0.0
pr(x::Dist) = pr(x, Cudd())

"A collection of errors that is thrown with some non-zero probability"
struct ProbException <: Exception
    errors::Vector{Tuple{AbstractFloat, ErrorException}}
end

function Base.showerror(io::IO, exc::ProbException)
    print(io, "ProbException: ")
    for (p, err) in exc.errors
        print(io, "  (")
        print(io, err)
        print(io, " with probability $p)")        
    end
end

function pr(x::MetaDist; ignore_errors=false)
    evidence = constraint(x)
    if !ignore_errors
        prerr = [(condpr(cond; evidence), err) for (cond,err) in errors(x)]
        filter!(y -> !iszero(y[1]), prerr)
        isempty(prerr) || throw(ProbException(prerr))
    end
    condpr(returnvalue(x); evidence)
end

"Compute a conditional probability"
condpr(x::Dist; evidence::AnyBool = true) = 
    pr(x & evidence) / pr(evidence) 

include("cudd.jl")