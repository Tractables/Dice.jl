export step_flip_probs, train_group_probs!, BoolToMax

struct BoolToMax
    bool::AnyBool
    evid::AnyBool
    weight::Real
    BoolToMax(bool, evid, weight) = new(bool & evid, evid, weight)
end

function BoolToMax(bool; evidence=true, weight=1)
    BoolToMax(bool, evidence, weight)
end

# Find the log-probabilities and the log-probability gradient of a BDD

sigmoid(x) = 1 / (1 + exp(-x))
deriv_sigmoid(x) = sigmoid(x) * (1 - sigmoid(x))


# Step flip probs in direction of gradient to maximize likelihood of BDDS
function step_flip_probs!(
    c::BDDCompiler,
    bdds_to_max::Vector{<:Tuple{CuddNode, CuddNode, <:Real}},
    learning_rate::AbstractFloat
)
    # Set flip probs according to groups
    global _flip_to_group
    global _group_to_psp

    # Find grad of logprobability w.r.t. each flip's probability
    w = WMC(c)
    grad = DefaultDict{Flip, Float64}(0.)
    for (bdd, obs_bdd, weight) in bdds_to_max
        isconstant(bdd) && continue
        gradhere = sub_dicts(grad_logprob(w, bdd), grad_logprob(w, obs_bdd))
        grad = add_dicts(grad, scale_dict(weight, gradhere))
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
    _group_to_psp = add_dicts(_group_to_psp, scale_dict(learning_rate, psp_grad_wrt_groups))
    propagate_group_probs!()
end

function train_group_probs!(
    bools_to_max::Vector{<:AnyBool},
    args...
)
    train_group_probs!(
        [BoolToMax(b, true, 1) for b in bools_to_max],
        args...
    )
end


# Train group_to_psp to such that generate() approximates dataset's distribution
function train_group_probs!(
    bools_to_max::Vector{BoolToMax},
    epochs::Integer=2000,
    learning_rate::AbstractFloat=0.003,
)
    # Compile to BDDs
    c = BDDCompiler(Iterators.flatten(map(x -> [x.bool, x.evid], bools_to_max)))
    bdds_to_max = [
        (compile(c, x.bool), compile(c, x.evid), x.weight)
        for x in bools_to_max
    ]
    for _ in 1:epochs
        step_flip_probs!(c, bdds_to_max, learning_rate)
    end
    nothing
end
