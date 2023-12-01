using Dice
using Distributions
using Plots

g = TruncatedNormal(0.0, 1.0, -8.0, 8.0)

discrete_gauss = Dict{Float64, Float64}()
start = -8.0
for i = 1:512
    discrete_gauss[start] = cdf(g, start + 0.125/4) - cdf(g, start)
    start = start+0.125/4
end
plot!(discrete_gauss)

t = DistFix{10, 5}
a = continuous(t, Normal(0, 1), 128, -8.0, 8.0)
b = pr(a)
plot(b)


g = Truncated(Normal(0, 1), -8.0, 8.0)

discrete_gauss = Dict{Float64, Float64}()
start = -8.0
for i = 1:512
    discrete_gauss[start] = cdf(g, start + 0.125/4) - cdf(g, start)
    start = start+0.125/4
end
plot!(discrete_gauss)
#

