using Revise
using Dice, Distributions
using DelimitedFiles

bits = ARGS[1]
pieces = ARGS[2]

DFiP = DistFixedPoint{8+bits, bits}

code = @dice begin
            engines = continuous(DFiP, Normal(5, 1), pieces, 0.0, 64.0)
            first_stage = continuous(DFiP, Normal(10, 3), pieces, 0.0, 64.0)
            completed_first_stage = engines + first_stage
            second_stage = continuous(DFiP, Normal(15, 3), pieces, 0.0, 64.0)
            completed_rocket = completed_first_stage + second_stage

            completed_rocket
end

p = expectation(code)

io = open(string("./benchmarks/spacex/results.txt"), "a")
@show bits, pieces, p
writedlm(io, [bits, pieces, p], ",")  
close(io)