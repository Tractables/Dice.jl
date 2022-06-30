using Dice
using Dice: num_flips, num_nodes, to_dice_ir
using Distributions
using StatsBase
using Distances

function KL_div(a, d::ContinuousUnivariateDistribution, upper, lower, interval)
    d = Truncated(d, upper, lower)
    len = Int((upper - lower)/interval)
    @assert len == length(a)
    p = Vector{Float64}(undef, len)
    for i=1:len
        p[i] = cdf(d, lower + i*interval) - cdf(d, lower + (i-1)*interval)
    end
        
    kldivergence(p, map(a->a[2], a))
end