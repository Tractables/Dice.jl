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
    errors::Vector{Tuple{AnyBool, String, Vector{Base.StackTraces.StackFrame}}}
    observations::Vector{AnyBool}
end

returnvalue(x) = x.returnvalue
observations(x) = x.observations
errors(x) = x.errors

constraint(x) = reduce(&, observations(x); init=true)

"A collection of errors that is thrown with some non-zero probability"
struct ProbException <: Exception
    errors::Vector{Tuple{AbstractFloat, String, Vector{Base.StackTraces.StackFrame}}}
end

function Base.showerror(io::IO, exc::ProbException)
    n = length(exc.errors)
    print(io, "ProbException: $(n) possible probabilistic error")
    n > 1 && print(io, "s")
    println(io)
    for (i, (p, msg, err_stacktrace)) in enumerate(exc.errors)
        showerror(io, ErrorException("#$(i): $(msg) with probability $(p)"), err_stacktrace)
    end
end

function pr(x::MetaDist; ignore_errors=false)
    evidence = constraint(x)
    if !ignore_errors
        prerr = [(condpr(cond; evidence),msg,err_stacktrace) for (cond,msg,err_stacktrace) in errors(x)]
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