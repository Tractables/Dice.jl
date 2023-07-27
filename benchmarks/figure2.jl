using Dice, Distributions
using Plots

d = TruncatedNormal(0, 1, -8, 8)

true_distribution = Dict{Float64, Float64}()
for i = 1:256
    lim = -8 + (i-1)*16/256
    true_distribution[lim] = cdf(d, lim + 16/256) - cdf(d, lim)
end
plot(true_distribution)


bit5 = Dict{Float64, Float64}()
for i = 1:32
    lim = -8 + (i-1)*16/32
    bit5[lim] = cdf(d, lim + 16/32) - cdf(d, lim)
end
scatter(bit5)