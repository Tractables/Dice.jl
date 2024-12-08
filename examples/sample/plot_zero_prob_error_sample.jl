# This file plots the number of zero probability samples as a function of bits being sampled

using Distributions
using LogExpFunctions
using DelimitedFiles
using Plots
include("ground_truth.jl")
include("data_generation.jl")
include("collapsed_sampling.jl")

io = open(string("plot_zero_prob_error_sample.txt"), "a") 

n = 5 # Number of observations
p = 2 # Number of features
X, y, beta = generate_linear(n, p)
mu, sigma = ground_truth_linear(X, y, [2 for _ in 1:p], 1)

for i in 1:7
    e, c = linear_regression_collapsed_sample(3, i, n, p, X, y, 100)
    @show n, p, i, c
    writedlm(io, [n p i c], ",")
end

n = 2 # Number of observations
p = 5 # Number of features
X, y, beta = generate_linear(n, p)
mu, sigma = ground_truth_linear(X, y, [2 for _ in 1:p], 1)

for i in 1:7
    e, c = linear_regression_collapsed_sample(3, i, n, p, X, y, 100)
    @show n, p, i, c
    writedlm(io, [n p i c], ",")
end

close(io)

# Plotting
lines = readdlm("plot_zero_prob_error_sample.txt", ',', Float64)
x52 = lines[1:7, 4]
x25 = lines[8:14, 4]
plot(x52, marker=:dot, labels = "2 features, 5 observations", xlabel="# bits sampled", ylabel="# samples with zero probability")
plot!(x25, marker=:dot, labels = "5 features, 2 observations")