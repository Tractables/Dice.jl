
export BoolToMax, mle_loss, kl_divergence

struct BoolToMax
    bool::AnyBool
    evid::AnyBool
    weight::Real
    BoolToMax(bool, evid, weight) = new(bool & evid, evid, weight)
end

function BoolToMax(bool; evidence=true, weight=1)
    BoolToMax(bool, evidence, weight)
end

function mle_loss(bools_to_max::Vector{BoolToMax})
    loss = 0
    for b in bools_to_max
        if b.evid === true
            loss -= b.weight * LogPr(b.bool)
        else
            loss -= b.weight * (LogPr(b.bool) - LogPr(b.evid))
        end
    end
    loss
end

function mle_loss(bools_to_max::Vector{<:AnyBool})
    mle_loss([BoolToMax(b, true, 1) for b in bools_to_max])
end

# This is valid but not what we usually want: when training a dist, the reference
# distribution should be constant, and the other should be symbolic.
# reference distribution to be constant.
# function kl_divergence(p::Dist, q::Dict{<:Any, <:Real}, domain::Set{<:Pair{<:Any, <:Dist}})
#     res = 0
#     for (x, x_dist) in domain
#         logpx = Var(prob_equals(p, x_dist)) # Var(b) represents the logpr of b
#         res += exp(logpx) * (logpx - log(q[x])) 
#     end
#     res
# end

function kl_divergence(p::Dict{<:Any, <:Real}, q::Dist, domain::Set{<:Pair{<:Any, <:Dist}})
    res = 0
    for (x, x_dist) in domain
        logqx = LogPr(prob_equals(q, x_dist))
        res += p[x] * (log(p[x]) - logqx) 
    end
    res
end