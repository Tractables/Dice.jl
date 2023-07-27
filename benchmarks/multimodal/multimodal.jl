using Dice, Distributions
using Revise
using Plots
using DelimitedFiles
using BenchmarkTools
using Plots

bits = 6
pieces = 256
DFiP = DistFixedPoint{6 + bits, bits}

mu1 = @dice continuous(DFiP, Normal(0, 1), pieces, -8.0, 8.0, true)
mu1 = continuous(DFiP, Normal(0, 1), pieces, -8.0, 8.0, true)
mu2 = continuous(DFiP, Normal(0, 1), pieces, -8.0, 8.0, true)

datapt = [5.0, 5.0, 5.0, 5.0, 5.0, 5.0, -5.0, -5.0, -5.0]

code = @dice begin
            for data in datapt
                y = ifelse(flip(2/3),
                                continuous(DFiP, Normal(0, 1), pieces, -8.0, 8.0, true) + mu1,
                                continuous(DFiP, Normal(0, 1), pieces, -8.0, 8.0, true) + mu2)
                observe(prob_equals(y, DFiP(data)))
                # ifelse(flip(2/3), 
                #             gaussian_observe(DFiP, pieces, -8.0, 8.0, mu1, 1.0, DFiP(data), add=true, exp=true),
                #             gaussian_observe(DFiP, pieces, -8.0, 8.0, mu2, 1.0, DFiP(data), add=true, exp=true))
            end
            (mu1)
        end

# expectation(mu1)

t = pr(code, ignore_errors=true)
plot(t, xlabel="mu1", ylabel="pr(mu1)", smooth=false, linewidth=5, guidefontsize=20, tickfontsize=10, legend=false)
savefig("multimodal.png")