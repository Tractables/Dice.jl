using Dice, Distributions
using Revise
using Plots
using DelimitedFiles
using BenchmarkTools

# bits = 19
# pieces = 8388608
# scale = 0.125

bits = parse(Int64, ARGS[1])
pieces = parse(Int64, ARGS[2])
scale = parse(Float64, ARGS[3])

DFiP = DistFixedPoint{7 + bits, bits}

a = ifelse(flip(0.5),
                laplace(DFiP, 0.0, scale, -8.0, 8.0), 
                laplace(DFiP, 1.0, scale, -7.0, 9.0))

data = [-0.5, -0.75, 0.75, 0.5]

t = @timed expectation(@dice begin
            for datapt in data
                gaussian_observe(DFiP, pieces, -8.0, 8.0, a, 1.0, DFiP(datapt), add=true, exp_arg=true)
            end
            a
end)

p = t.value
io = open(string("./benchmarks/laplace_scaling/results_")*string(scale*1000)*string(".txt"), "a")
@show bits, pieces, p, t.time
writedlm(io, [bits pieces p t.time], ",")  
close(io)

