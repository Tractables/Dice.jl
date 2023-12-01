using Revise
using Dice, Distributions
using DelimitedFiles
using BenchmarkTools

bits = parse(Int64, ARGS[1])
pieces = parse(Int64, ARGS[2])

p = pr(@dice uniform(DistUInt{3}))

DFiP = DistFix{8+bits, bits}

t = @timed expectation(@dice begin
            engines = continuous(DFiP, Normal(5, 1), pieces, 0.0, 64.0)
            first_stage = continuous(DFiP, Normal(10, 3), pieces, 0.0, 64.0, true)
            completed_first_stage = engines + first_stage
            second_stage = continuous(DFiP, Normal(15, 3), pieces, 0.0, 64.0, true)
            completed_rocket = completed_first_stage + second_stage

            completed_rocket
end)

p = t.value

io = open(string("./benchmarks/spacex/results.txt"), "a")
@show bits, pieces, p, t.time
writedlm(io, [bits pieces p t.time], ",")  
close(io)