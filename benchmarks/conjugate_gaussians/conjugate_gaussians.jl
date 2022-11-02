using Revise
using Dice, Distributions
using DelimitedFiles
using BenchmarkTools

bits = parse(Int64, ARGS[1])
pieces = parse(Int64, ARGS[2])

p = pr(@dice uniform(DistUInt{3}))

DFiP = DistFixedPoint{5 + bits, bits}

data = DFiP.([1.0, 2.0])
add_arg = true

t = @timed expectation(@dice begin
                a = continuous(DFiP, Normal(0, 1), pieces, -8.0, 8.0)
                for datapt in data
                    gaussian_observe(DFiP, pieces, -8.0, 8.0, a, 1.0, datapt, add=add_arg)
                    @show datapt
                end
                a
            end)

p = t.value

io = open(string("./benchmarks/conjugate_gaussians/results.txt"), "a")
@show bits, pieces, p, t.time
writedlm(io, [bits pieces p t.time], ",")  
close(io)