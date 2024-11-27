using Distributions
using LogExpFunctions
include("ground_truth.jl")
include("data_generation.jl")
include("bitblast.jl")

n = 10
p = 3
X, y, beta = generate_linear(n, p)
mu, sigma = ground_truth_linear(X, y, [2 for _ in 1:p], 1)

linear_regression_bitblast(5, n, p, X, y)

