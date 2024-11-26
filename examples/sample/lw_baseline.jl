using Distributions
using LogExpFunctions
include("ground_truth.jl")
include("data_generation.jl")
include("likelihood_weighting.jl")

n = 10
p = 3
X, y, beta = generate_linear(n, p)
mu, sigma = ground_truth_linear(X, y, [2 for _ in 1:p], 1)

NSAMPLES = 100000
value = Vector(undef, NSAMPLES)
weights = Vector(undef, NSAMPLES)
for i in 1:NSAMPLES
    value[i], weights[i] = linear_model(X, y)
end

adj_weights = weights .- logsumexp(weights)
reduce(+, value .* exp.(adj_weights))
ess = 1/sum(exp.(adj_weights).^2)

