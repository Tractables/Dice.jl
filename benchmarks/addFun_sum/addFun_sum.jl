using Revise
using Dice, Distributions
using DelimitedFiles
using BenchmarkTools

if length(ARGS) == 0
    bits = 18
    pieces = 128
else
    bits = parse(Int64, ARGS[1])
    pieces = parse(Int64, ARGS[2])
end

DFiP = DistFix{5+bits, bits}
indices = [1, 0, 1]

t = @timed expectation(@dice begin
                x = Vector(undef, 3)
                for i=1:3
                    x[i] = bitblast(DFiP, Normal(0, 1), pieces, -8.0, 8.0)
                end
                sum = DFiP(0.0)
                for i=1:3
                    sum = ifelse(indices[i] == 1, sum + x[i], sum)
                end
                sum
end)

p = t.value

io = open(string("./benchmarks/addFun_sum/results.txt"), "a")
@show bits, pieces, p, t.time
writedlm(io, [bits pieces p t.time], ",")  
close(io)