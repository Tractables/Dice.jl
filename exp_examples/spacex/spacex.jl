using Revise
using Dice, Distributions
using DelimitedFiles
using BenchmarkTools
using Plots

bits = parse(Int64, ARGS[1])
pieces = parse(Int64, ARGS[2])
bits = 19
pieces = 32
p = pr(@dice uniform(DistUInt{3}))

DFiP = DistFixedPoint{9+bits, bits}

t = pr(@dice begin
            engines = continuous(DFiP, Normal(5, 5), pieces, 0.0, 64.0)
            first_stage = continuous(DFiP, Normal(10, 5), pieces, 0.0, 64.0)
            completed_first_stage = engines + first_stage
            second_stage = continuous(DFiP, Normal(16, 8), pieces, 0.0, 64.0)
            completed_rocket = completed_first_stage + second_stage

            engines
            # first_stage
            # completed_first_stage
            # second_stage
            # completed_rocket
end)

plot(filter((a -> first(a) < 75), t), line=(:solid), label="engines", xaxis="x",yaxis="pr(x)",xguidefontsize=30, yguidefontsize=30, xtickfontsize=15, ytickfontsize=15, legendfont=15)
plot!(filter((a -> first(a) < 75), t), line=(:solid), label="completed_first_stage")
plot!(filter((a -> first(a) < 75), t), line=(:solid), label="first_stage")
plot!(filter((a -> first(a) < 75), t), line=(:solid), label="second_stage")
plot!(filter((a -> first(a) < 75), t), line=(:solid), label="completed_rocket")
plot!(filter((a -> first(a) < 75), t), line = (:solid), label="completed_rocket", linewidth=5, xaxis = ("x"), yaxis = ("pr(x)"), xguidefontsize=30, xtickfontsize=15, yguidefontsize=30, ytickfontsize=15)
p = t.value

io = open(string("./benchmarks/spacex/results.txt"), "a")
@show bits, pieces, p, t.time
writedlm(io, [bits pieces p t.time], ",")  
close(io)

savefig("output_example1.png")