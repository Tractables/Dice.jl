using Revise
using Dice, Distributions
using DelimitedFiles

bits = ARGS[1]
pieces = ARGS[2]
bits = 2
pieces = 8
DFiP = DistFixedPoint{5 + bits, bits}

data = DFiP.([1.0, 2.0])
add_arg = true

code = @dice begin
                a = continuous(DFiP, Normal(0, 1), 16, -8.0, 8.0)
                for datapt in data
                    gaussian_observe(DFiP, 16, -8.0, 8.0, a, 1.0, datapt, add=add_arg)
                end
                a
            end

p = expectation(code)

io = open(string("./benchmarks/conjugate_gaussians/results.txt"), "a")
@show bits, pieces, p
writedlm(io, [bits pieces p], ",")  
close(io)