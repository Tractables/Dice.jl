# Find the log-probabilities and the log-probability gradient of a BDD

# Calculate dict from BDD node to its log-probability
#   flip_probs: flip id -> probability
#   flip_to_prob_group: map flip to corresponding prob group
function logprob(
    bdds::Vector{CuddNode},
    flip_probs::Dict{<:Any, Float64},
    level_to_prob_group::Dict{<:Integer, <:Any},
)
    cache = Dict{CuddNode,Float64}()
    terminal = get_one(bdds[1])
    cache[terminal] = log(one(Float64))
    cache[not(terminal)] = log(zero(Float64))

    rec(x) = 
        get!(cache, x) do
            prob = flip_probs[level_to_prob_group[level(x)]]
            a = log(prob) + rec(high(x))
            b = log(1.0-prob) + rec(low(x))
            if (!isfinite(a))
                b
            elseif (!isfinite(b))
                a
            else
                # log(exp(a) + exp(y))
                # https://www.wolframalpha.com/input?i=log%28e%5Ex%2Be%5Ey%29+-+%28max%28x%2C+y%29+%2B+log%281+%2B+e%5E%28-%7Cx-y%7C%29%29
                max(a,b) + log1p(exp(-abs(a-b)))
            end
        end
    
    for bdd in bdds
        rec(bdd)
    end
    cache
end

# Calculate gradient of a BDD node w.r.t. flip probabilities (reverse mode)
function grad_logprob(
    bdd::CuddNode,
    flip_probs::Dict{<:Any, Float64},
    level_to_prob_group::Dict{<:Integer, <:Any},
    logprobs::Dict{CuddNode, Float64},
)
    grad = Dict(pg => 0.0 for pg in keys(flip_probs))
    deriv = Dict{CuddNode, Float64}()
    deriv[bdd] = 1
    level_traversal(bdd) do node
        i, lo, hi = level(node), low(node), high(node)
        pg = level_to_prob_group[i]
        prob = flip_probs[pg]
        fhi, flo = logprobs[hi], logprobs[lo]
        get!(deriv, hi, 0)
        get!(deriv, lo, 0)
        denom = prob * exp(fhi) + (1 - prob) * exp(flo)
        deriv[hi] += deriv[node] * prob * exp(fhi) / denom
        deriv[lo] += deriv[node] * (1 - prob) * exp(flo) / denom
        grad[pg] += deriv[node] * (exp(fhi) - exp(flo)) / denom
    end
    grad
end

# Step flip probs in direction of gradient to maximize likelihood of BDDS
function step_flip_probs(
    flip_probs::Dict{<:Any, Float64},
    prob_groups,
    bdds_to_maximize::Vector{CuddNode},
    level_to_prob_group::Dict{<:Integer, <:Any},
    learning_rate::AbstractFloat
)
    total_grad = Dict(pg => 0. for pg in prob_groups)
    logprobs = logprob(bdds_to_maximize, flip_probs, level_to_prob_group)
    for bdd in bdds_to_maximize
        @assert !is_constant(bdd)
        total_grad += grad_logprob(bdd, flip_probs, level_to_prob_group, logprobs)
    end
    # Add as we want to maximize probability
    flip_probs = flip_probs + learning_rate * total_grad
    clamp!(flip_probs, 0, 1)
    flip_probs
end
