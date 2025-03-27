using Revise
using Alea, Distributions
using DelimitedFiles
using BenchmarkTools

if length(ARGS) == 0
    bits = 18
    pieces = 32
else
    bits = parse(Int64, ARGS[1])
    pieces = parse(Int64, ARGS[2])
end

DFiP = DistFix{5+bits, bits}

t = @timed expectation(@alea begin
                x = bitblast(DFiP, Normal(0, 1), pieces, -8.0, 8.0)
                y = bitblast(DFiP, Normal(0, 1), pieces, -8.0, 8.0)
                m = if (x < y) y else x end
                m
end)

p = t.value

io = open(string("./benchmarks/addFun_max/results.txt"), "a")
@show bits, pieces, p, t.time
writedlm(io, [bits pieces p t.time], ",")  
close(io)