using Dice, Distributions
using DelimitedFiles
using BenchmarkTools

bits = parse(Int64, ARGS[1])
pieces = parse(Int64, ARGS[2])

p = pr(@dice uniform(DistUInt{3}))

t = @timed pr(@dice begin
    DFiP = DistFixedPoint{bits + 5, bits}

            alice_skill = continuous(DFiP, Normal(5, 1), pieces, -3.0, 13.0, true)
            bob_skill = continuous(DFiP, Normal(5, 1), pieces, -3.0, 13.0, true)

            alice_skill = continuous(DFiP, Normal(5, 1), pieces, -3.0, 13.0, true)
            bob_skill = continuous(DFiP, Normal(5, 1), pieces, -3.0, 13.0, true)

            lazy_lag = DFiP(2.0)

            match = Vector(undef, 5)

            for i = 1:5
                match[i] = (ifelse(flip(1/3), alice_skill - lazy_lag, alice_skill) < (ifelse(flip(1/3), bob_skill - lazy_lag, bob_skill)))
                # match[i] = alice_skill < bob_skill
            end

            observe(match[1])
            observe(!match[2])
            observe(match[3])
            observe(!match[4])
            match[5]
        end)

p = t.value

io = open(string("./benchmarks/tug_of_war/results.txt"), "a")
@show bits, pieces, p[1.0], t.time
writedlm(io, [bits pieces p[1.0] t.time], ",")  
close(io)