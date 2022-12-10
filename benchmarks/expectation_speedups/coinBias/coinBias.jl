using Revise
using Dice, Distributions
using DelimitedFiles
using BenchmarkTools

p = pr(@dice uniform(DistUInt{3}))

# bits = parse(Int64, ARGS[1])
# pieces = parse(Int64, ARGS[2])
bits=20
pieces = 4096
DFiP = DistFixedPoint{bits+2, bits}

y = [1, 1, 0, 1, 0]

code = (@dice begin
        a = continuous(DFiP, Beta(2, 5), pieces, 0.0, 1.0)
        for i = 1:5
            b = parametrised_flip(a)
            observe((y[i]!=1) | b)
            observe((y[i]==1) | !b)
        end
        return a
end)

t1 = @benchmark begin
    temp = pr(code)
    e = reduce(+, [(key*value) for (key, value) in temp])
end

t2 = @benchmark begin
    temp = expectation(code)
    # e = reduce(+, [(key*value) for (key, value) in temp])
end

t3 = @benchmark begin
    temp = pr(code)
    e = reduce(+, [(key*value) for (key, value) in temp])
    v = reduce(+, [(key*key*value) for (key, value) in temp]) - e^2
end

t4 = @benchmark begin
    temp = variance(code)
    # e = reduce(+, [(key*value) for (key, value) in temp])
end


@show "coinBias", median(t1).time, median(t2).time, median(t3).time, median(t4).time

# p = t.value
# io = open(string("./benchmarks/coinBias/results.txt"), "a")
# @show bits, pieces, p, t.time
# writedlm(io, [bits pieces p t.time], ",")  
# close(io)