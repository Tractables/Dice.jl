using Revise
using Dice, Distributions
using DelimitedFiles
using BenchmarkTools
using Plots

if length(ARGS) == 0
    bits = 16
    pieces = 2048
else
    bits = parse(Int64, ARGS[1])
    pieces = parse(Int64, ARGS[2])
end

DFiP = DistFix{8 + bits, bits}

data = DFiP.([8.0, 9.0])
add_arg = true

t = @timed expectation(@dice begin
                a = bitblast(DFiP, Normal(0, 1), pieces, -16.0, 16.0)
                for datapt in data
                    gaussian_observe(DFiP, pieces, -16.0, 16.0, a, 1.0, datapt, add=add_arg, exp=false)
                end
                a
            end)

# plot(t.value)

p = t.value
io = open(string("./benchmarks/conjugate_gaussians/results_new.txt"), "a")
@show bits, pieces, p, t.time
writedlm(io, [bits pieces p t.time], ",")  
close(io)

