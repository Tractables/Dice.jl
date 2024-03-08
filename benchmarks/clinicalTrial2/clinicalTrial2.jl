using Revise
using Dice, Distributions
using DelimitedFiles
using BenchmarkTools

if length(ARGS) == 0
    bits = 10
else
    bits = parse(Int64, ARGS[1])
end

DFiP = DistFix{2+bits, bits}

controlGroup = [false, false, true, false, false]
treatedGroup = [true, false, true, true, true]

t = @timed expectation(@dice begin
            isEffective = flip(0.5)
            probIfTreated = uniform(DFiP, 0.0, 1.0)
            probIfControl = if isEffective uniform(DFiP, 0.0, 1.0) else probIfTreated end

            for i=1:5
                controlFlip = parametrised_flip(probIfControl)
                observe(controlFlip == controlGroup[i])
                treatedFlip = parametrised_flip(probIfTreated)
                observe(treatedFlip == treatedGroup[i])
            end

            observe(isEffective)
            probIfControl
end)


p = t.value

io = open(string("./benchmarks/clinicalTrial2/results_new.txt"), "a")
@show bits, p, t.time
writedlm(io, [bits p t.time], ",")  
close(io)