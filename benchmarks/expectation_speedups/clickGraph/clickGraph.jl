using Revise
using Dice, Distributions
using DelimitedFiles
using BenchmarkTools

# bits = parse(Int64, ARGS[1])
bits=6
p = pr(@dice uniform(DistUInt{3}))

DFiP = DistFixedPoint{2+bits, bits}

clicks0 = [true, true, true, false, false]
clicks1 = [true, true, true, false, false]

sim0 = Vector(undef, 5)
sim1 = Vector(undef, 5)

# code = 

# t = expectation(code)

t1 = @benchmark begin
    temp = pr(@dice (begin
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
end))
    e = reduce(+, [(key*value) for (key, value) in temp])
end

t2 = @benchmark begin
    temp = expectation(@dice (begin
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
end))
    # e = reduce(+, [(key*value) for (key, value) in temp])
end

t3 = @benchmark begin
    temp = pr(@dice (begin
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
end))
    e = reduce(+, [(key*value) for (key, value) in temp])
    v = reduce(+, [(key*key*value) for (key, value) in temp]) - e^2
end

t4 = @benchmark begin
    temp = variance(@dice (begin
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
end))
    # e = reduce(+, [(key*value) for (key, value) in temp])
end


@show "clickGraph", median(t1).time, median(t2).time, median(t3).time, median(t4).time