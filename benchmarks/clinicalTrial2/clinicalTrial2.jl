using Revise
using Dice, Distributions
using DelimitedFiles
using BenchmarkTools

bits = parse(Int64, ARGS[1])

# bits = 3
p = pr(@dice uniform(DistUInt{3}))

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

io = open(string("./benchmarks/clinicalTrial2/results.txt"), "a")
@show bits, p, t.time
writedlm(io, [bits p t.time], ",")  
close(io)