using Alea
using Distributions
using Plots
using Revise
using BenchmarkTools

pieces = [2^i for i in 1:9]

function kl_divergence(p, q)
    @assert sum(p) ≈ 1.0
    @assert sum(q) ≈ 1.0
    ans = 0
    @show length(p)
    for i=1:length(p)
        if p[i] > 0
            ans += p[i] *(log(p[i]) - log(q[i]))
        end
    end
    ans
end

d = truncated(Normal(0, 1), -8.0, 8.0)
lower = -8.0
q = Vector{Float64}(undef, 2^10)
for i=1:2^10
    q[i] = (cdf(d, lower + 1/2^6) - cdf(d, lower))
    lower += 1/2^6
end 
sum(q)

kld_linear = Vector(undef, 9)
kld_exp = Vector(undef, 9)
time_linear = Vector(undef, 9)
time_exp = Vector(undef, 9)


map(pieces) do piece
    @show piece
    y = bitblast(DistFix{13, 6}, Normal(0, 1), piece, -8.0, 8.0)
    p_linear = pr(y)

    z = bitblast_exponential(DistFix{13, 6}, Normal(0, 1), piece, -8.0, 8.0)
    p_exp = pr(z)

    p_linear = map(a -> a[2], sort([(k, v) for (k, v) in p_linear]))
    kld_linear[Int(log2(piece))] = kl_divergence(p_linear, q)

    p_exp = map(a -> a[2], sort([(k, v) for (k, v) in p_exp]))
    kld_exp[Int(log2(piece))] = kl_divergence(p_exp, q)
end

@show kld_linear
@show kld_exp

map(pieces) do piece
    linear = median(@benchmark p_linear = pr(bitblast(DistFix{13, 6}, Normal(0, 1), $piece, -8.0, 8.0))).time
    expo = median(@benchmark p_exp = pr(bitblast_exponential(DistFix{13, 6}, Normal(0, 1), $piece, -8.0, 8.0))).time

    time_linear[Int(log2(piece))] = linear
    time_exp[Int(log2(piece))] = expo
end

@show time_linear
@show time_exp

plot(time_linear, kld_linear, xaxis=:log, yaxis=:log, marker=:dot, label="linear", xlabel="time", ylabel="KLD", title="Accuracy-Time plot", annot=pieces)
plot!(time_exp, kld_exp, xaxis=:log, yaxis=:log, marker=:dot, label="exp", xlabel="time", ylabel="KLD", title="Accuracy-Time plot", annot=pieces)
# plot(pieces, kld_exp, xaxis=:log, yaxis=:log, marker=:dot, legend=false, xlabel="Number of pieces", ylabel="KL divergence", xguidefontsize=20, yguidefontsize=20)
savefig("continuous_experiments/linear_vs_exponential.png")

# Plot gaussian
y = bitblast(DistFix{13, 6}, Normal(0, 1), 4, -8.0, 8.0)
p_linear = pr(y)
p_linear = map(a -> log(a[2]), sort([(k, v) for (k, v) in p_linear]))

z = bitblast_exponential(DistFix{13, 6}, Normal(0, 1), 4, -8.0, 8.0)
p_exp = pr(z)
p_exp = map(a -> log(a[2]), sort([(k, v) for (k, v) in p_exp]))

plot(p_exp, label="exponential")
plot!(p_linear, label="linear")
plot!(q, label="true")
savefig("continuous_experiments/visualizing_approx.png")
