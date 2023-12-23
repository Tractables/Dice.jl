##################################
# CUDD Inference
##################################

export WMC

using DataStructures: LinkedList, cons, nil

ADFloat = Union{AbstractFloat, ADNode}

mutable struct WMC
    c::BDDCompiler
    cache::Dict{CuddNode, ADFloat}
    function WMC(c)
        w = new(c, Dict{CuddNode, ADFloat}())
        w.cache[constant(w.c.mgr, true)] = log(one(Float64))
        w.cache[constant(w.c.mgr, false)] = log(zero(Float64))
        w
    end
end

logprob(w::WMC, x::AnyBool) = logprob(w, compile(w.c, x))

function logprob(w::WMC, x::CuddNode)
    get!(w.cache, x) do
        f = w.c.level_to_flip[level(x)]
        a = log(f.prob) + logprob(w, high(x))
        b = log(1.0-f.prob) + logprob(w, low(x))
        log(exp(a) + exp(b))
    end
end
