using Revise
using Dice, Distributions
using DelimitedFiles
using BenchmarkTools

# bits = parse(Int64, ARGS[1])

bits = 9
p = pr(@dice uniform(DistUInt{3}))

DFiP = DistFixedPoint{2+bits, bits}

controlGroup = [false, false, true, false, false]
treatedGroup = [true, false, true, true, true]

# code = ()

t1 = @benchmark begin
    temp = pr(@dice begin
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
    e = reduce(+, [(key*value) for (key, value) in temp])
end

t2 = @benchmark begin
    temp = expectation(@dice begin
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
    # e = reduce(+, [(key*value) for (key, value) in temp])
end

t3 = @benchmark begin
    temp = pr(@dice begin
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
    e = reduce(+, [(key*value) for (key, value) in temp])
    v = reduce(+, [(key*key*value) for (key, value) in temp]) - e^2
end

t4 = @benchmark begin
    temp = variance(@dice begin
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
    # e = reduce(+, [(key*value) for (key, value) in temp])
end


@show "clinicalTrial2", median(t1).time, median(t2).time, median(t3).time, median(t4).time


# p = t.value

# io = open(string("./benchmarks/clinicalTrial2/results.txt"), "a")
# @show bits, p, t.time
# writedlm(io, [bits p t.time], ",")  
# close(io)