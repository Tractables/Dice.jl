using Revise
using Dice, Distributions
using DelimitedFiles
using BenchmarkTools

precision = parse(Int64, ARGS[1])
num_pieces = parse(Int64, ARGS[2])

p = pr(@dice uniform(DistUInt{3}))

DFiP = DistFixedPoint{8+precision, precision}

data = DFiP.([1.0, 3.0, 5.0, 7.0, 9.0]);


code = @timed expectation(@dice begin
    x = DFiP(0.0)
    v = DFiP(0.0)
    a = DFiP(0.0)
    for datapt in data
        x += v
        observe(!(x < DFiP(0.0)))
        observe(!(DFiP(9.0) < x))
        v += continuous(DFiP, Normal(0, 1), num_pieces, -8.0, 8.0)
        o = x + continuous(DFiP, Normal(0, 1), num_pieces, -8.0, 8.0)
        observe(o == datapt)
    end
    x
end)

# code = @dice begin
#     x = DFiP(0.0)
#     v = DFiP(0.0)
#     # a = DFiP(0.0)
#     for datapt in data
#         x += v
#         observe(!(x < DFiP(0.0)))
#         observe(!(DFiP(15.0) < x))
#         v += continuous(DFiP, Normal(0, 1), num_pieces, -8.0, 8.0)
#         # a += continuous(DFiP, Normal(0, 1), num_pieces, -8.0, 8.0)
#         o = x + continuous(DFiP, Normal(0, 1), num_pieces, -8.0, 8.0)
#         observe(o == datapt)
#     end
#     x
# end;

t = code
p = t.value
io = open(string("./benchmarks/kalman/results.txt"), "a")
@show precision, num_pieces, p, t.time
writedlm(io, [precision num_pieces p t.time], ",")  
close(io)