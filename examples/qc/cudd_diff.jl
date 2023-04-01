# Find the log-probabilities and the log-probability gradient of a BDD

sigmoid(x) = 1 / (1 + exp(-x))
sigmoid_deriv(x) = sigmoid(x) * (1 - sigmoid(x))

# Calculate dict from BDD node to its log-probability
#   group_to_psp: Prob group to psp ("pre-sigmoid probability")
#   level_to_group: map CUDD level to corresponding group
function logprob(
    bdds::Vector{CuddNode},
    group_to_psp::Dict{<:Any, Float64},
    level_to_group::Dict{<:Integer, <:Any},
)
    cache = Dict{CuddNode,Float64}()
    terminal = get_one(bdds[1])
    cache[terminal] = log(one(Float64))
    cache[not(terminal)] = log(zero(Float64))

    rec(x) = 
        get!(cache, x) do
            prob = sigmoid(group_to_psp[level_to_group[level(x)]])
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
    group_to_psp::Dict{<:Any, Float64},
    level_to_group::Dict{<:Integer, <:Any},
    logprobs::Dict{CuddNode, Float64},
)
    grad = Dict(group => 0.0 for group in keys(group_to_psp))
    deriv = Dict{CuddNode, Float64}()
    deriv[bdd] = 1
    level_traversal(bdd) do node
        i, lo, hi = level(node), low(node), high(node)
        group = level_to_group[i]
        psp = group_to_psp[group]
        prob = sigmoid(psp)
        fhi, flo = logprobs[hi], logprobs[lo]
        get!(deriv, hi, 0)
        get!(deriv, lo, 0)
        denom = prob * exp(fhi) + (1 - prob) * exp(flo)
        deriv[hi] += deriv[node] * prob * exp(fhi) / denom
        deriv[lo] += deriv[node] * (1 - prob) * exp(flo) / denom
        grad[group] += deriv[node] * sigmoid_deriv(psp) * (exp(fhi) - exp(flo)) / denom
    end
    grad
end

# Step flip probs in direction of gradient to maximize likelihood of BDDS
function step_flip_probs(
    group_to_psp::Dict{<:Any, Float64},
    bdds_to_maximize::Vector{CuddNode},
    level_to_group::Dict{<:Integer, <:Any},
    learning_rate::AbstractFloat
)
    total_grad = Dict(group => 0. for group in keys(group_to_psp))
    logprobs = logprob(bdds_to_maximize, group_to_psp, level_to_group)
    for bdd in bdds_to_maximize
        @assert !is_constant(bdd)
        total_grad += grad_logprob(bdd, group_to_psp, level_to_group, logprobs)
    end
    # Add as we want to maximize probability
    group_to_psp + learning_rate * total_grad
end
