using Dice, Distributions
using Revise
using Plots
using DelimitedFiles
using BenchmarkTools
using Plots


bits = 5
pieces = 256
scale = 0.015625/2

DFiP = DistFix{7+ bits, bits}

w1 = laplace(DFiP, 0.0, scale, -8.0, 8.0)
w2 = laplace(DFiP, 0.0, scale, -8.0, 8.0)


data = [1.0]

t = pr(@dice begin
            mu = w1 + w2
            gaussian_observe(DFiP, pieces, -8.0, 8.0, mu, 1.0, DFiP(1.0), add=true)
            w1
end)

plot(t)
p = t.value

expectation(w1)


io = open(string("results_blr")*string(scale*1000)*string(".txt"), "a")
@show bits, pieces, p, t.time
writedlm(io, [bits pieces p t.time], ",")  
close(io)