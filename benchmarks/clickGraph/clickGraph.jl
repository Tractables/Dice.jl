using Revise
using Dice, Distributions
using DelimitedFiles
using BenchmarkTools

if length(ARGS) == 0
    bits = 8
else
    bits = parse(Int64, ARGS[1])
end

DFiP = DistFix{2+bits, bits}

clicks0 = [true, true, true, false, false]
clicks1 = [true, true, true, false, false]

sim0 = Vector(undef, 5)
sim1 = Vector(undef, 5)

t = @timed expectation(@dice begin
            similarityAll = uniform(DFiP, 0.0, 1.0)
            for i=1:5
                sim = parametrised_flip(similarityAll)
                beta1 = uniform(DFiP, 0.0, 1.0)
                beta2 = ifelse(sim, beta1, uniform(DFiP, 0.0, 1.0))
                sim0[i] = parametrised_flip(beta1)
                sim1[i] = parametrised_flip(beta2)
            end

            for i=1:5
                observe(sim0[i] == clicks0[i])
                observe(sim1[i] == clicks1[i])
            end
            similarityAll
end)

p = t.value

io = open(string("./benchmarks/clickGraph/results_new.txt"), "a")
@show bits, p, t.time
writedlm(io, [bits p t.time], ",")  
close(io)