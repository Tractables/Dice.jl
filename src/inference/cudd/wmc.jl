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

logprob(w::WMC, x::AnyBool) = logprob(w, compile(w.c, x))

function logprob(w::WMC, x::CuddNode, vals=nothing)
    get!(w.cache, x) do
        f = w.c.level_to_flip[level(x)]
        p = if f.prob isa ADNode
            compute(f.prob, vals)
        else
            f.prob
        end
        a = log(p) + logprob(w, high(x), vals)
        b = log(1.0-p) + logprob(w, low(x), vals)
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
function grad_logprob(w::WMC, x::CuddNode, vals=nothing)::Dict{Flip, Float64}
    grad = DefaultDict{Flip, Float64}(0.)
    deriv = DefaultDict{CuddNode, Float64}(0.)
    deriv[x] = 1
    level_traversal(x) do node
        i, lo, hi = level(node), low(node), high(node)
        f = w.c.level_to_flip[i]
        fhi, flo = logprob(w, hi, vals), logprob(w, lo, vals)
        p = if f.prob isa ADNode
            compute(f.prob, vals)
        else
            f.prob
        end
        denom = p * exp(fhi) + (1 - p) * exp(flo)
        deriv[hi] += deriv[node] * p * exp(fhi) / denom
        deriv[lo] += deriv[node] * (1 - p) * exp(flo) / denom
        grad[f] += deriv[node] * (exp(fhi) - exp(flo)) / denom
    end
    grad
end

