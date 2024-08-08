using Dice, Distributions
using Revise
using Plots
using DelimitedFiles
using BenchmarkTools
using Plots


bits = 10
DFiP = DistFix{4 + bits, bits}

s = Vector(undef, 8)
for i in 0:7
    s[i+1] = 1/2^i
end

distrib1 = ifelse(flip(0.5), laplace(DFiP, 0.0, s[4], -2.0, 2.0), laplace(DFiP, 1.0, s[4], -1.0, 3.0))
plot(pr(distrib1), xlabel="x", ylabel="pr(x)", label="s = 0.125", title="Laplace Distributions")
distrib2 = ifelse(flip(0.5), laplace(DFiP, 0.0, s[5], -2.0, 2.0), laplace(DFiP, 1.0, s[5], -1.0, 3.0))
plot!(pr(distrib2), label="s = 0.0625")
savefig("Laplace_plot.png")

