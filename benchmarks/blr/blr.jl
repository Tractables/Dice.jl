using Dice, Distributions
using Revise
using Plots
using DelimitedFiles
using BenchmarkTools
using Plots


bits = 5
pieces = 256
scale = 0.015625/2

bits = parse(Int64, ARGS[1])
pieces = parse(Int64, ARGS[2])
scale = parse(Float64, ARGS[3])

DFiP = DistFixedPoint{7+ bits, bits}

w1 = laplace(DFiP, 0.0, scale, -8.0, 8.0)
w2 = laplace(DFiP, 0.0, scale, -8.0, 8.0)


data = [1.0]

t = pr(@dice begin
            mu = w1 + w2
            observe(prob_equals(mu, DFiP(1.0)))
            # gaussian_observe(DFiP, pieces, -8.0, 8.0, mu, 1.0, DFiP(1.0), add=true)
            w2
end)

plot(t)
p = t.value

expectation(w1)


io = open(string("./benchmarks/blr/results_")*string(scale*1000)*string(".txt"), "a")
@show bits, pieces, p, t.time
writedlm(io, [bits pieces p t.time], ",")  
close(io)