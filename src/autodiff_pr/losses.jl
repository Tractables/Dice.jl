export BoolToMax, mle_loss, kl_divergence, neg_entropy

struct BoolToMax
    bool::AnyBool
    evid::AnyBool
    weight::Real
    BoolToMax(b; evidence=true, weight=1) = new(b & evidence, evidence, weight)
end

function mle_loss(bools_to_max::Vector{BoolToMax})
    -1 * sum(bools_to_max) do b
        if b.evid === true
            b.weight * LogPr(b.bool)
        else
            b.weight * (LogPr(b.bool) - LogPr(b.evid))
        end
    end
end
mle_loss(bools::Vector{<:AnyBool}) = mle_loss([BoolToMax(b) for b in bools])

function kl_divergence(p::Dict{<:Any, <:Real}, q::Dist, domain::Set{<:Pair{<:Any, <:Dist}})
    sum(domain) do (x, x_dist)
        logqx = LogPr(prob_equals(q, x_dist))
        p[x] * (log(p[x]) - logqx) 
    end
end

function neg_entropy(p::Dist, domain::Set{<:Dist})
    sum(domain) do x
        LogPr(prob_equals(p, x)) * exp(LogPr(prob_equals(p, x)))
    end
end
