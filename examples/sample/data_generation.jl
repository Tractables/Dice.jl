using Distributions
using Random
using StatsBase

# n Number of observations
# p Number of parameters
# s Sparsity parameter
function generate_spike_slab(n, p, s)
    X = rand(Normal(0, 1), n, p)

    dt = fit(ZScoreTransform, X, dims=1, center=true, scale=true)
    X_new = StatsBase.transform(dt, X)

    beta = [if i <= s 2 else 0 end for i in 1:p]

    epsilon = 2*rand(Normal(0, 1), n)

    y = X_new*beta + epsilon
    return X_new, y, beta
end

# Ground truth betas are 2
# Ground truth noise variance is 2
function generate_linear(n, p)
    X = rand(Normal(0, 1), n, p)

    dt = fit(ZScoreTransform, X, dims=1, center=true, scale=true)
    X_new = StatsBase.transform(dt, X)

    beta = [2 for i in 1:p]

    epsilon = 2*rand(Normal(0, 1), n)

    y = X_new*beta + epsilon
    return X_new, y, beta
end

