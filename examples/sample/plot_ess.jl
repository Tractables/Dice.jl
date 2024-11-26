using Plots
using DelimitedFiles

lines = readdlm("ess.txt", ',', Float64)

w1 = lines[1:8, :]
w2 = lines[9:16, :]
error = lines[17:24, :]

plot(w1[:, 2], w1[:, 5], label="w1", yaxis=:log, xlabel="The bit being sampled", ylabel="Effective sample size", marker="o")
plot!(w2[:, 2], w2[:, 5], label="w2", marker="o")
plot!(error[:, 2], error[:, 5], label="error", marker="o")