using Revise
using Dice, Distributions
using DelimitedFiles
using BenchmarkTools

if length(ARGS) == 0
    bits = 4
    pieces = 32
else
    bits = parse(Int64, ARGS[1])
    pieces = parse(Int64, ARGS[2])
end

t = @timed pr(@dice begin
    DFiP = DistFix{bits + 6, bits}

            # alice_skill = bitblast(DFiP, Normal(0, 1), pieces, -8.0, 8.0)
            # bob_skill = bitblast(DFiP, Normal(0, 1), pieces, -8.0, 8.0)

            alice_skill = bitblast(DFiP, Normal(0, 1), pieces, -8.0, 8.0)
            bob_skill = bitblast(DFiP, Normal(0, 1), pieces, -8.0, 8.0)

            # lazy_lag = DFiP(2.0)

            match = Vector(undef, 3)

            for i = 1:3
                # match[i] = (ifelse(flip(1/3), alice_skill - lazy_lag, alice_skill) < (ifelse(flip(1/3), bob_skill - lazy_lag, bob_skill)))
                match[i] = (bitblast(DFiP, Normal(0, 2), pieces, -16.0, 16.0) + alice_skill) < (bitblast(DFiP, Normal(0, 2), pieces, -16.0, 16.0) + bob_skill)
                # match[i] = alice_skill < bob_skill
            end

            observe(match[1])
            observe(!match[2])
            # observe(match[3])
            # observe(!match[4])
            match[3]
        end)

p = t.value

io = open(string("./benchmarks/trueskill/results_new.txt"), "a")
@show bits, pieces, p[1.0], t.time
writedlm(io, [bits pieces p[1.0] t.time], ",")  
close(io)
        