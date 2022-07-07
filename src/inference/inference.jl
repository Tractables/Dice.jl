export pr, condpr, Cudd, ProbException

##################################
# Inference with metadata
##################################

"Compute probability of a Dice.jl program"
pr(x) = pr(x, default_infer_algo())

"Compute a conditional probability"
condpr(x::Dist; evidence::AnyBool = true) = 
    # TODO: simplify x based on evidence; propagate values 
    pr(x & evidence) / pr(evidence) 

##################################
# Inference with metadata
##################################

"A distribution computed by a dice program with metadata on observes and errors"
struct MetaDist
    returnvalue::Dist
    errors::Vector{Tuple{AnyBool, ErrorException}}
    observations::Vector{AnyBool}
end

returnvalue(x) = x.returnvalue
observations(x) = x.observations
errors(x) = x.errors

constraint(x) = reduce(&, observations(x); init=true)

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

##################################
# Inference backends
##################################

struct Cudd <: InferAlgo end
default_infer_algo() = Cudd()

include("cudd.jl")