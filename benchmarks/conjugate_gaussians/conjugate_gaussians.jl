using Revise
using Alea, Distributions
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

t = @timed pr(@alea begin
                a = bitblast(DFiP, Normal(0, 1), pieces, -16.0, 16.0)
                for datapt in data
                    gaussian_observe(DFiP, pieces, -16.0, 16.0, a, 1.0, datapt, add=add_arg, exp=false)
                end
                a
            end)

plot(t.value)

# Writing result to a text file
result = Dict{Float64, Float64}()
for i in 1.0:0.1:8.0
    result[i] = 0.0
end
for (key, value) in t.value
    if (key > 1) & (key < 8.1)
        result[floor(key*10)/10] += value
    end
end
io = open("./benchmarks/conjugate_gaussians/conjugate_gaussians_16_2048.txt", "w")
writedlm(io, [value for (key, value) in sort(result)])
close(io)

