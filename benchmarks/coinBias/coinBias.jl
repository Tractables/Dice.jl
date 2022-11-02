using Revise
using Dice, Distributions
using DelimitedFiles
using BenchmarkTools

p = pr(@dice uniform(DistUInt{3}))

bits = parse(Int64, ARGS[1])
pieces = parse(Int64, ARGS[2])

DFiP = DistFixedPoint{bits+2, bits}

y = [1, 1, 0, 1, 0]

t = @timed expectation(@dice begin
        a = continuous(DFiP, Beta(2, 5), pieces, 0.0, 1.0)
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