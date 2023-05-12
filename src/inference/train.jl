export step_flip_probs, train_group_probs!

# Find the log-probabilities and the log-probability gradient of a BDD

sigmoid(x) = 1 / (1 + exp(-x))
deriv_sigmoid(x) = sigmoid(x) * (1 - sigmoid(x))

# Step flip probs in direction of gradient to maximize likelihood of BDDS
function step_flip_probs!(
    c::BDDCompiler,
    cond_bdds_to_maximize::Vector{Tuple{CuddNode, CuddNode}},
    learning_rate::AbstractFloat
)
    # Set flip probs according to groups
    global _flip_to_group
    global _group_to_psp
    for (f, group) in _flip_to_group
        f.prob = sigmoid(_group_to_psp[group])
    end

    # Find grad of logprobability w.r.t. each flip's probability
    w = WMC(c)
    grad = DefaultDict{Flip, Float64}(0.)
    for (bdd, obs_bdd) in cond_bdds_to_maximize
        isconstant(bdd) && continue
        grad += grad_logprob(w, bdd) - grad_logprob(w, obs_bdd)
    end

    # Convert to grad of pre-sigmoid probabilities w.r.t. each group's
    # pre-sigmoid probability. Let "f" denote a flip, "g" denote a group.
    #
    # δlogpr/δg.psp = Σ_{f∈g} δlogpr/δf.pr * δf.pr/δg.psp
    #               = Σ_{f∈g} δlogpr/δf.pr * σ'(g.psp)        (as f.pr=σ(g.psp))
    psp_grad_wrt_groups = DefaultDict{Any, Float64}(0.)
    for (f, group) in _flip_to_group
        haskey(grad, f) || continue
        dpdf = grad[f]
        psp_grad_wrt_groups[group] += dpdf * deriv_sigmoid(_group_to_psp[group])
    end
    _group_to_psp += learning_rate * psp_grad_wrt_groups
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