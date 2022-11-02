using Revise
using Dice, Distributions
using DelimitedFiles
using BenchmarkTools
using Plots
using LinearAlgebra, ForwardDiff
import PyPlot
import Contour: contours, levels, level, lines, coordinates

precision = parse(Int64, ARGS[1])
num_pieces = parse(Int64, ARGS[2])
precision = 3
num_pieces = 32
p = pr(@dice uniform(DistUInt{3}))

DFiP = DistFixedPoint{8+precision, precision}

datax = DFiP.([1.0, 3.0, 5.0, 7.0, 9.0]);
datay = DFiP.([1.0, 3.0, 5.0, 7.0, 9.0]);



code = @dice begin
    x = DFiP(0.0)
    # y = DFiP(0.0)
    v = DFiP(0.0)
    # vy = DFiP(0.0)
    for datapt in datax
        x += v
        observe(!(x < DFiP(0.0)))
        observe(!(DFiP(9.0) < x))
        v += continuous(DFiP, Normal(0, 1), num_pieces, -8.0, 8.0)
        o = x + continuous(DFiP, Normal(0, 1), num_pieces, -8.0, 8.0)
        observe(o == datapt)
    end
    # for datapt in datay
    #     y += vy
    #     observe(!(y < DFiP(0.0)))
    #     observe(!(DFiP(9.0) < y))
    #     vy += continuous(DFiP, Normal(0, 1), num_pieces, -8.0, 8.0)
    #     oy = y + continuous(DFiP, Normal(0, 1), num_pieces, -8.0, 8.0)
    #     observe(oy == datapt)
    # end
    x
end

p = pr(code)


xs = filter(i -> (i > 7), sort([i for i in keys(p)]))
ys = filter(i -> (i > 7), sort([i for i in keys(p)]))
f(x, y) = p[x]*p[y]
surface(xs, ys, f,xlabel = "x", ylabel = "y", zlabel = "pr(x, y)", color=:gist_earth)
savefig("fig3.png")
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