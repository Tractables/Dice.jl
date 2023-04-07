using Dice, Distributions
using Plots
using DelimitedFiles
using BenchmarkTools

function kl_divergence(p, q)
    @assert sum(p) ≈ 1.0
    @assert sum(q) ≈ 1.0
    ans = 0
    for i=1:length(p)
        if p[i] > 0
            ans += p[i] *(log(p[i]) - log(q[i]))
        end
    end
    ans
end

gt = Vector(undef, 1025)
d = Normal(512, 16)
counter = 0
for i in 0:1024
    counter += 1
    gt[counter] = cdf(d, i+1) - cdf(d, i)
end

for i = 0:10
    times = 2^i
    range = Float64(2^(10 - i)) + 1.0
    @show times, range
    c = @timed (begin
                    code = @dice begin
                                DFiP = DistFixedPoint{12, 0}
                                a = uniform(DFiP, 0.0, range)
                                for j = 1:times - 1
                                    a += uniform(DFiP, 0.0, range)
                                end
                            a
                    end
                    p = pr(code)
                    p
                end)
    @show c
    p = c.value
    a = sort(collect(p), by = x -> x[1])
    x = map(x -> x[2], a)

    k = kl_divergence(gt, x)
    io = open(string("./scratch/clt_results.txt"), "a")
    @show times, range, k, c.time
    writedlm(io, [times range k c.time], ",")  
    close(io)
end


p = pr(code)

# (times, range) = (1, 1025.0)
# c = Trial(17.891 ms)
# (times, range) = (2, 513.0)
# c = Trial(37.160 ms)
# (times, range) = (4, 257.0)
# c = Trial(200.969 ms)
# (times, range) = (8, 129.0)
# c = Trial(752.122 ms)
# (times, range) = (16, 65.0)
# c = Trial(2.182 s)
# (times, range) = (32, 33.0)
# c = Trial(5.823 s)
# (times, range) = (64, 17.0)
# c = Trial(16.890 s)
# (times, range) = (128, 9.0)
# c = Trial(47.895 s)
# (times, range) = (256, 5.0)
# c = Trial(129.443 s)
# (times, range) = (512, 3.0)
# c = Trial(369.576 s)
# (times, range) = (1024, 2.0)
# c = Trial(729.535 s)