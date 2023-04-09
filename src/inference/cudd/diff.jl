# Find the log-probabilities and the log-probability gradient of a BDD

sigmoid(x) = 1 / (1 + exp(-x))
sigmoid_deriv(x) = sigmoid(x) * (1 - sigmoid(x))

# Calculate gradient of a BDD node w.r.t. flip probabilities (reverse mode)
function grad_logprob(w::WMC, x::CuddNode)
    grad = Dict(group => 0.0 for group in keys(w.group_to_psp))
    deriv = Dict{CuddNode, Float64}()
    deriv[bdd] = 1
    level_traversal(bdd) do node
        i, lo, hi = level(node), low(node), high(node)
        f = w.c.level_to_flip[i]
        prob = get_flip_prob(w, f)
        fhi, flo = logprob(w, hi), logprob(w, lo)
        get!(deriv, hi, 0)
        get!(deriv, lo, 0)
        denom = prob * exp(fhi) + (1 - prob) * exp(flo)
        deriv[hi] += deriv[node] * prob * exp(fhi) / denom
        deriv[lo] += deriv[node] * (1 - prob) * exp(flo) / denom
        if haskey(w.flip_to_group, f)
            group = w.flip_to_group[f]
            psp = w.group_to_psp[group]
            grad[group] += deriv[node] * sigmoid_deriv(psp) * (exp(fhi) - exp(flo)) / denom
        end
    end
    grad
end

# Step flip probs in direction of gradient to maximize likelihood of BDDS
function step_flip_probs(
    w::WMC,
    cond_bdds_to_maximize::Vector{Tuple{CuddNode, CuddNode}},
    learning_rate::AbstractFloat
)
    total_grad = Dict(group => 0. for group in keys(group_to_psp))
    for (bdd, obs_bdd) in cond_bdds_to_maximize
        is_constant(bdd) && continue
        total_grad += grad_logprob(w, bdd) - grad_logprob(w, obs_bdd)
    end
    w.group_to_psb += learning_rate * total_grad
end
