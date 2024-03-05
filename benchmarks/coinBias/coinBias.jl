using Revise
using Dice, Distributions
using DelimitedFiles
using BenchmarkTools

if length(ARGS) == 0
    bits = 20
    pieces = 512
else
    bits = parse(Int64, ARGS[1])
    pieces = parse(Int64, ARGS[2])
end

DFiP = DistFix{bits+2, bits}

y = [1, 1, 0, 1, 0]

t = @timed expectation(@dice begin
        a = bitblast_exponential(DFiP, Beta(2, 5), pieces, 0.0, 1.0)
        for i = 1:5
            b = parametrised_flip(a)
            observe((y[i]!=1) | b)
            observe((y[i]==1) | !b)
        end
        return a
end)

p = t.value
io = open(string("./benchmarks/coinBias/results.txt"), "a")
@show bits, pieces, p, t.time
writedlm(io, [bits pieces p t.time], ",")  
close(io)