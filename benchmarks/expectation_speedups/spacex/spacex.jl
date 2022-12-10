using Revise
using Dice, Distributions
using DelimitedFiles
using BenchmarkTools

# bits = parse(Int64, ARGS[1])
# pieces = parse(Int64, ARGS[2])

bits=11
pieces=2048

p = pr(@dice uniform(DistUInt{3}))

DFiP = DistFixedPoint{8+bits, bits}

code = (@dice begin
            engines = continuous(DFiP, Normal(5, 1), pieces, 0.0, 64.0)
            first_stage = continuous(DFiP, Normal(10, 3), pieces, 0.0, 64.0)
            completed_first_stage = engines + first_stage
            second_stage = continuous(DFiP, Normal(15, 3), pieces, 0.0, 64.0)
            completed_rocket = completed_first_stage + second_stage

            completed_rocket
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


@show "spacex", median(t1).time, median(t2).time, median(t3).time, median(t4).time

# p = t.value

# io = open(string("./benchmarks/spacex/results.txt"), "a")
# @show bits, pieces, p, t.time
# writedlm(io, [bits pieces p t.time], ",")  
# close(io)