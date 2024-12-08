using Distributions
using LogExpFunctions
include("ground_truth.jl")
include("data_generation.jl")
include("collapsed_sampling.jl")

n = 2 # Number of observations
p = 5 # Number of features
X, y, beta = generate_linear(n, p)
mu, sigma = ground_truth_linear(X, y, [2 for _ in 1:p], 1)

linear_regression_collapsed_sample(5, 3, n, p, X, y, 100)
