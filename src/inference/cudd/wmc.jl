##################################
# CUDD Inference
##################################

export WMC

using DataStructures: LinkedList, cons, nil

mutable struct WMC
    c::BDDCompiler
    cache::Dict{CuddNode, Float64}
    function WMC(c)
        w = new(c, Dict{CuddNode, Float64}())
        w.cache[constant(w.c.mgr, true)] = log(one(Float64))
        w.cache[constant(w.c.mgr, false)] = log(zero(Float64))
        w
    end
end

function logprob(w::WMC, x::CuddNode)
    get!(w.cache, x) do
        f = w.c.level_to_flip[level(x)]
        a = log(f.prob) + logprob(w, high(x))
        b = log(1.0-f.prob) + logprob(w, low(x))
        if isinf(a)
            b
        elseif isinf(b)
            a
        else
            # log(exp(a) + exp(y))
            max(a,b) + log1p(exp(-abs(a-b)))
        end
    end
end

# Calculate gradient of a BDD node w.r.t. flip probabilities (reverse mode)
function grad_logprob(w::WMC, x::CuddNode)::Dict{Flip, Float64}
    grad = DefaultDict{Flip, Float64}(0.)
    deriv = DefaultDict{CuddNode, Float64}(0.)
    deriv[x] = 1
    level_traversal(x) do node
        i, lo, hi = level(node), low(node), high(node)
        f = w.c.level_to_flip[i]
        fhi, flo = logprob(w, hi), logprob(w, lo)
        denom = f.prob * exp(fhi) + (1 - f.prob) * exp(flo)
        deriv[hi] += deriv[node] * f.prob * exp(fhi) / denom
        deriv[lo] += deriv[node] * (1 - f.prob) * exp(flo) / denom
        grad[f] += deriv[node] * (exp(fhi) - exp(flo)) / denom
    end
    grad
end

