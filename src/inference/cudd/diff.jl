export step_flip_probs, train_group_probs!

# Find the log-probabilities and the log-probability gradient of a BDD

sigmoid(x) = 1 / (1 + exp(-x))
sigmoid_deriv(x) = sigmoid(x) * (1 - sigmoid(x))

# Calculate gradient of a BDD node w.r.t. flip probabilities (reverse mode)
function grad_logprob(w::WMC, x::CuddNode)
    grad = Dict(group => 0.0 for group in keys(w.group_to_psp))
    deriv = Dict{CuddNode, Float64}()
    deriv[x] = 1
    level_traversal(x) do node
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
function step_flip_probs!(
    c::BDDCompiler,
    cond_bdds_to_maximize::Vector{Tuple{CuddNode, CuddNode}},
    learning_rate::AbstractFloat
)
    global _group_to_psp
    w = WMC(
        c,
        _group_to_psp,  # global (todo: lift references to this to edges of API)
        _flip_to_group,  # global (todo: lift references to this to edges of API)
    )
    total_grad = Dict(group => 0. for group in keys(w.group_to_psp))
    for (bdd, obs_bdd) in cond_bdds_to_maximize
        isconstant(bdd) && continue
        total_grad += grad_logprob(w, bdd) - grad_logprob(w, obs_bdd)
    end
    _group_to_psp += learning_rate * total_grad
    nothing
end

function train_group_probs!(bools_to_maximize::Vector{<:AnyBool}, args...)
    train_group_probs!(
        [(b, true) for b in bools_to_maximize],
        args...
    )
end

# Train group_to_psp to such that generate() approximates dataset's distribution
function train_group_probs!(
    cond_bools_to_maximize::Vector{<:Tuple{<:AnyBool, <:AnyBool}},
    epochs::Integer=1000,
    learning_rate::AbstractFloat=0.3,
)
    # Compile to BDDs
    cond_bools_to_maximize = [
        (x & evid, evid)
        for (x, evid) in cond_bools_to_maximize
    ]
    c = BDDCompiler(Iterators.flatten(cond_bools_to_maximize))
    cond_bdds_to_maximize = [
        (compile(c, conj), compile(c, obs))
        for (conj, obs) in cond_bools_to_maximize
    ]
    for _ in 1:epochs
        step_flip_probs!(c, cond_bdds_to_maximize, learning_rate)
    end
    nothing
end