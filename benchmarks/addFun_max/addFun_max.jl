using Revise
using Dice, Distributions
using DelimitedFiles
using BenchmarkTools

bits = parse(Int64, ARGS[1])
pieces = parse(Int64, ARGS[2])

bits = 8
pieces = 16
p = pr(@dice uniform(DistUInt{3}))

DFiP = DistFix{5+bits, bits}

t = @timed expectation(@dice begin
                x = bitblast(DFiP, Normal(0, 1), pieces, -8.0, 8.0)
                y = bitblast(DFiP, Normal(0, 1), pieces, -8.0, 8.0)
                m = if (x < y) y else x end
                m
end)
@show median(t).time
p = t.value

io = open(string("./benchmarks/addFun_max/results.txt"), "a")
@show bits, pieces, p, t.time
writedlm(io, [bits pieces p t.time], ",")  
close(io)