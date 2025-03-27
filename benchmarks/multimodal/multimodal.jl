using Alea, Distributions
using Revise
using Plots
using DelimitedFiles
using BenchmarkTools
using Plots

bits = 6
pieces = 256
DFiP = DistFix{7 + bits, bits}

mu1 = uniform(DFiP, -16.0, 16.0)
mu2 = uniform(DFiP, -16.0, 16.0)

datapt = [5.0, 5.0, 5.0, 5.0, 5.0, 5.0, -5.0, -5.0, -5.0]

code = @dice begin
            for data in datapt
                y = ifelse(flip(2/3),
                                bitblast_exponential(DFiP, Normal(0, 1), pieces, -8.0, 8.0) + mu1,
                                bitblast_exponential(DFiP, Normal(0, 1), pieces, -8.0, 8.0) + mu2)
                observe(prob_equals(y, DFiP(data)))
            end
            (mu1)
        end

# Plotting the query result
t = pr(code, ignore_errors=true)
plot(t, xlabel="mu1", ylabel="pr(mu1)", smooth=false, linewidth=5, guidefontsize=20, tickfontsize=10, legend=false)
savefig("./benchmarks/multimodal/multimodal_6_256.png")

# Writing result to a text file
t_new = filter(a -> (a[1] >= -8) & (a[1] < 8), t)
io = open("./benchmarks/multimodal/multimodal_6_256.txt", "w")
writedlm(io, [value for (key, value) in sort([(k, v) for (k, v) in t_new])])
close(io)