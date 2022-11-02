using Revise
using Dice, Distributions
using DelimitedFiles
using BenchmarkTools

precision = parse(Int64, ARGS[1])
num_pieces = parse(Int64, ARGS[2])

p = pr(@dice uniform(DistUInt{3}))

DFiP = DistFixedPoint{8+precision, precision}

truncation = (-8.0, 8.0)
add_arg = true

xs = DFiP.([1.0, 2.0, 3.0, 4.0, 5.0]);
ys = DFiP.([2.02305151081, 2.54221660051, 3.00165586221, 1.91956623397, 0.712648052222])

code = @timed pr(@dice begin
            z1 = flip(0.5)
            z2 = flip(0.5)
            b1 = if z1 DFiP(0.0) else continuous(DFiP, Normal(0, 1), num_pieces, -8.0, 8.0) end
            b2 = if z2 DFiP(0.0) else continuous(DFiP, Normal(0, 1), num_pieces, -8.0, 8.0) end
            for (x, y) in zip(xs, ys)
                mean = x*b1 + b2
                gaussian_observe(DFiP, num_pieces, truncation[1], truncation[2], mean, 1.0, y, add=add_arg)
            end
            z1
end)

t = code
p = t.value
io = open(string("./benchmarks/spike_and_slab/results.txt"), "a")
@show precision, num_pieces, p, t.time
writedlm(io, [precision num_pieces p t.time], ",")  
close(io)