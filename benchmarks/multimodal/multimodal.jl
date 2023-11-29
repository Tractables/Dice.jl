using Dice, Distributions
using Revise
using Plots
using DelimitedFiles
using BenchmarkTools
using Plots

bits = 6
pieces = 256
DFiP = DistFixedPoint{7 + bits, bits}

mu1 = uniform(DFiP, -16.0, 16.0)
mu2 = uniform(DFiP, -16.0, 16.0)

datapt = [5.0, 5.0, 5.0, 5.0, 5.0, 5.0, -5.0, -5.0, -5.0]

code = @dice begin
            for data in datapt
                y = ifelse(flip(2/3),
                                continuous(DFiP, Normal(0, 1), pieces, -8.0, 8.0, true) + mu1,
                                continuous(DFiP, Normal(0, 1), pieces, -8.0, 8.0, true) + mu2)
                observe(prob_equals(y, DFiP(data)))
                # if flip(2/3) 
                #             gaussian_observe(DFiP, pieces, -8.0, 8.0, mu1, 1.0, DFiP(data), add=true, exp=true)
                # else           gaussian_observe(DFiP, pieces, -8.0, 8.0, mu2, 1.0, DFiP(data), add=true, exp=true)
                # end
            end
            (mu1)
        end


t = pr(code, ignore_errors=true)
plot(t, xlabel="mu1", ylabel="pr(mu1)", smooth=false, linewidth=5, guidefontsize=20, tickfontsize=10, legend=false)
savefig("multimodal_4_128.png")

t_new = filter(a -> (a[1] >= -8) & (a[1] < 8), t)
io = open("multimodal_6_256.txt", "w")
writedlm(io, [value for (key, value) in sort([(k, v) for (k, v) in t_new])])
close(io)

x = Dict{Float64, Float64}()
for i in -8.0:0.1:7.9
    sum = 0
    for j in i:0.015625:(i+0.1 - 0.015625)
        sum = sum + t[j]
    end
    x[i] = sum
end








# Results for MCMC

  


