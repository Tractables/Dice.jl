using Dice, Distributions
using Revise
using Plots
using DelimitedFiles
using BenchmarkTools
using Plots


bits = 0
DFiP = DistFixedPoint{4 + bits, bits}
s = 3.0
distrib = laplace(DFiP, 0.0, s, -8.0, 8.0)
# plot(pr(distrib))
pr(prob_equals(distrib, DFiP(3*2^(-60))))

exponential(DFiP, -3.0, 0.0, 8.0)


# bits = 10
# pieces = 1024
# scale = 0.015625

bits = parse(Int64, ARGS[1])
pieces = parse(Int64, ARGS[2])
scale = parse(Float64, ARGS[3])

DFiP = DistFixedPoint{7 + bits, bits}

a = ifelse(flip(0.5),
                laplace(DFiP, 0.0, scale, -8.0, 8.0), 
                laplace(DFiP, 1.0, scale, -7.0, 9.0))

data = [-0.5, -0.75, 1.75, 1.5]

t = @timed expectation(@dice begin
            for datapt in data
                # prob_equals(laplace(DFiP, 0.0, 1.0, -8.0, 8.0) + a, DFiP(datapt))
                gaussian_observe(DFiP, pieces, -8.0, 8.0, a, 1.0, DFiP(datapt), add=true, exp=true)
                
            end
            a
end)

p = t.value
io = open(string("./benchmarks/laplace_scaling/results_")*string(scale*1000)*string(".txt"), "a")
@show bits, pieces, p, t.time
writedlm(io, [bits pieces p t.time], ",")  
close(io)

# p = pr(a)
# plot(filter(a -> a[1] < 2, p))
# savefig("laplace_plot.png")
