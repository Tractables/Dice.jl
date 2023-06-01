using Dice, Distributions
using Revise
using Plots
using DelimitedFiles
using BenchmarkTools
using Plots

# bits = 0
# pieces = 16
# n_vars = 3

bits = parse(Int64, ARGS[1])
pieces = parse(Int64, ARGS[2])
n_vars = parse(Int64, ARGS[3])

DFiP = DistFixedPoint{5 + bits, bits}

z = Vector(undef, n_vars)
y = Vector(undef, n_vars)
z[1] = discrete(DistUInt{2}, [1/3, 1/3, 1/3])

t = @timed expectation(@dice begin
        for i in 2:n_vars
            z[i] = ifelse(prob_equals(z[i-1], DistUInt{2}(0)),
                                discrete(DistUInt{2}, [1/3, 1/3, 1/3]),
                                ifelse(prob_equals(z[i-1], DistUInt{2}(1)),
                                    discrete(DistUInt{2}, [1/3, 1/3, 1/3]),
                                    discrete(DistUInt{2}, [1/3, 1/3, 1/3])))
        end

        mu1 = continuous(DFiP, Normal(0, 1), pieces, -8.0, 8.0, true)
        mu2 = continuous(DFiP, Normal(0, 1), pieces, -8.0, 8.0, true)
        mu3 = continuous(DFiP, Normal(0, 1), pieces, -8.0, 8.0, true)

        for i in 1:n_vars
            a = ifelse(prob_equals(z[i], DistUInt{2}(0)),
                        gaussian_observe(DFiP, pieces, -8.0, 8.0, mu1, 1.0, DFiP(0.5), add=true, exp=true),
                        ifelse(prob_equals(z[i], DistUInt{2}(1)),
                                gaussian_observe(DFiP, pieces, -8.0, 8.0, mu2, 1.0, DFiP(0.5), add=true, exp=true),
                                gaussian_observe(DFiP, pieces, -8.0, 8.0, mu3, 1.0, DFiP(0.5), add=true, exp=true)))
        end

        mu1
end)

p = t.value
io = open(string("./benchmarks/hmm_slicstan/results_")*string(n_vars)*string(".txt"), "a")
@show bits, pieces, p, t.time
writedlm(io, [bits pieces p t.time], ",")  
close(io)