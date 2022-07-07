export pr, condpr, Cudd, ProbException, allobservations

##################################
# Core inference API implemented by backends
##################################

"A choice of probabilistic inference algorithm"
abstract type InferAlgo end

"A query for the joint state of several bits"
const JointQuery = Vector{AnyBool}

"A query supported by the inference backend"
const Query = Union{JointQuery, AnyBool}

"An error with a probabilistic condition"
const CondError = Tuple{AnyBool, ErrorException}

"""
Compute probabilities of queries, optionally given evidence, 
conditional errors, and a custom inference algorithm.
"""
function condprobs(queries; evidence::AnyBool = true, 
            errors::Vector{CondError} = CondError[], 
            algo::InferAlgo = default_infer_algo()) 
    condprobs(algo, evidence, errors, queries)
end

"""
Compute probability of a single query, optionally given evidence, 
conditional errors, and a custom inference algorithm.
"""
function condprob(query; evidence::AnyBool = true, 
            errors::Vector{CondError} = CondError[], 
            algo::InferAlgo = default_infer_algo()) 
    condprobs([query]; evidence, errors, algo)[1]
end

"""
Compute probability of a single query, 
optionally with conditional errors, and a custom inference algorithm.
"""
function pr(query;
            errors::Vector{CondError} = CondError[], 
            algo::InferAlgo = default_infer_algo()) 
    condprob(query; errors, algo)
end

##################################
# Inference with metadata distributions from DSL
##################################
       
"A distribution computed by a dice program with metadata on observes and errors"
struct MetaDist
    returnvalue::Dist
    errors::Vector{CondError}
    observations::Vector{AnyBool}
end

returnvalue(x) = x.returnvalue
observations(x) = x.observations
allobservations(x) = reduce(&, observations(x); init=true)

function pr(x::MetaDist; ignore_errors=false, 
            algo::InferAlgo = default_infer_algo())
    evidence = allobservations(x)
    errors = ignore_errors ? CondError[] : x.errors
    condprob(returnvalue(x); evidence, errors, algo)
end

##################################
# Prbabilistic exception support
##################################

"An error that is thrown with some non-zero probability"
const ProbError = Tuple{Float64, ErrorException}

"A collection of errors that is thrown with some non-zero probability"
struct ProbException <: Exception
    errors::Vector{ProbError}
end

function Base.showerror(io::IO, exc::ProbException)
    print(io, "ProbException: ")
    for (p, err) in exc.errors
        print(io, "  (")
        print(io, err)
        print(io, " with probability $p)")        
    end
end

##################################
# Inference backends
##################################

include("cudd.jl")