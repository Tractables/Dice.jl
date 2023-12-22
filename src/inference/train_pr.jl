# The bridge between autodiff and cudd
export step_vars!, train_pr!, total_logprob, valuation_to_flip_pr_resolver
using DataStructures: Queue

struct LogPr <: Variable
    bool::Dist{Bool}
end


# Find the log-probabilities and the log-probability gradient of a BDD
function add_scaled_dict!(
    x::AbstractDict{<:Any, <:Real},
    y::AbstractDict{<:Any, <:Real},
    s::Real
)
    for (k, v) in y
        x[k] += v * s
    end
end


function step_pr!(
    var_vals::Valuation,
    loss::ADNode,
    learning_rate::Real
)
    # loss refers to logprs of bools
    # error to do with LogPr(true)? just make it a vector of anybool and don't filter
    bools = Vector{Dist{Bool}}([
        n.bool for n in variables(loss)
        if !(n isa Var) && !(n.bool isa Bool)
    ])

    # so, calculate these logprs
    w = WMC(BDDCompiler(bools), valuation_to_flip_pr_resolver(var_vals))
    bool_logprs = Valuation(LogPr(bool) => logprob(w, bool) for bool in bools)
    # TODO: have differentiate return vals as well to avoid this compute
    # or have it take vals
    loss_val = compute(bool_logprs, [loss])[loss] # for return value only

    # so we can move the blame from to loss to those bools
    derivs = differentiate(bool_logprs, Derivs(loss => 1))

    # find grad of loss w.r.t. each flip's probability
    grad = DefaultDict{Flip, Float64}(0.)
    for bool in bools
        add_scaled_dict!(grad, grad_logprob(w, bool), derivs[LogPr(bool)])
    end

    # move blame from flips probabilities to their adnode params
    root_derivs = Derivs()
    for (f, d) in grad
        if f.prob isa ADNode
            if haskey(root_derivs, f.prob)
                root_derivs[f.prob] += d
            else
                root_derivs[f.prob] = d
            end
        end
    end

    # move blame from adnode params to vars
    derivs = differentiate(var_vals, root_derivs)

    # update vars
    for (adnode, d) in derivs
        if adnode isa Var
            var_vals[adnode] -= d * learning_rate
        end
    end
    loss_val
end

# Train group_to_psp to such that generate() approximates dataset's distribution
function train_pr!(
    var_vals::Valuation,
    loss::ADNode;
    epochs::Integer,
    learning_rate::Real,
)
    losses = []
    for _ in 1:epochs
        push!(losses, step_pr!(var_vals, loss, learning_rate))
    end
    push!(losses, compute_loss(var_vals, loss))
    losses
end

function valuation_to_flip_pr_resolver(var_vals)
    vals = Dict{ADNode, ADNodeCompatible}()
    merge!(vals, var_vals)
    function flip_pr_resolver(prob)
        compute_one(prob, vals)
    end   
end

function compute_loss(
    var_vals::Valuation,
    loss::ADNode
)
    bools = Vector{Dist{Bool}}([
        n.bool for n in variables(loss)
        if !(n isa Var) && !(n.bool isa Bool)
    ])
    w = WMC(BDDCompiler(bools), valuation_to_flip_pr_resolver(var_vals))
    bool_logprs = Valuation(LogPr(bool) => logprob(w, bool) for bool in bools)
    compute(bool_logprs, [loss])[loss] # for return value only
end
