using Revise
using Dice, Distributions
using DelimitedFiles
using BenchmarkTools
using Plots

bits = parse(Int64, ARGS[1])
pieces = parse(Int64, ARGS[2])

bits = 16
pieces = 2048

p = pr(@dice uniform(DistUInt{3}))

DFiP = DistFix{6 + bits, bits}

data = DFiP.([8.0, 9.0])
add_arg = true

t = expectation(@dice begin
                a = continuous(DFiP, Normal(0, 1), pieces, -8.0, 8.0, true)
                for datapt in data
                    gaussian_observe(DFiP, pieces, -8.0, 8.0, a, 1.0, datapt, add=add_arg, exp=false)
                    @show datapt
                end
                a
            end)

plot(t)



p = t.value

io = open(string("./benchmarks/conjugate_gaussians/results.txt"), "a")
@show bits, pieces, p, t.time
writedlm(io, [bits pieces p t.time], ",")  
close(io)