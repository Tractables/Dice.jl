using Dice, Distributions
using Plots
using DelimitedFiles
using BenchmarkTools

function kl_divergence(p, q)
    @assert sum(p) ≈ 1.0
    @assert sum(values(q)) ≈ 1.0
    ans = 0
    # for i=1:length(p)
    #     if p[i] > 0
    #         ans += p[i] *(log(p[i]) - log(q[i]))
    #     end
    # end
    for i=1:1024
        if p[i] > 0
            c = if q[i-1] == 0 10^(-224) else q[i-1] end
            ans += p[i] *(log(p[i]) - log(c))
            @show ans, i, p[i] *(log(p[i]) - log(c))
        end
    end
    ans
end

gt = Vector(undef, 1024)
d = Normal(512, 16)
# counter = 0
for i in 0:1023
    gt[i+1] = cdf(d, i+1) - cdf(d, i)
end

for i = 0:10
    # i = 1
    pieces = 2^i
    @show pieces
    c = @timed (begin
                    code = @dice begin
                                DFiP = DistFixedPoint{12, 0}
                                a = continuous(DFiP, Normal(512, 16), pieces, 0.0, 1024.0)
                                a
                    end
                    p = pr(code)
                    p
                end)
    # @show c
    p = c.value
    a = sort(collect(p), by = x -> x[1])
    x = map(x -> x[2], a)

    k = kl_divergence(gt, p)
    io = open(string("./scratch/lpa_results.txt"), "a")
    @show pieces k, c.time
    writedlm(io, [pieces k c.time], ",")  
    close(io)
end

# pieces = 1
# c = Trial(17.572 ms)
# pieces = 2
# c = Trial(21.737 ms)
# pieces = 4
# c = Trial(13.895 ms)
# pieces = 8
# c = Trial(12.471 ms)
# pieces = 16
# c = Trial(11.035 ms)
# pieces = 32
# c = Trial(11.544 ms)
# pieces = 64
# c = Trial(13.443 ms)
# pieces = 128
# c = Trial(17.268 ms)
# pieces = 256
# c = Trial(25.604 ms)
# pieces = 512
# c = Trial(42.737 ms)

