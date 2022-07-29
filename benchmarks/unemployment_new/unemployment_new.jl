using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir
using Distributions
using StatsBase
using Distances
using Plots

function unemployment(p::Int, binbits::Int, flag::Int)
    code = @dice begin
        y = [3.33008960302557, 5.19543854472405, 5.88929762709886, 5.52449264517973, 5.31172037906861]
        y_lag = [4.3838241041638, 3.93442675489932, 7.57050890065729, 4.53683034032583, 5.28768584504724]

        t_g = DistSigned{binbits + 5, binbits}
        t_g_4 = DistSigned{binbits + 8, binbits + 3}
        t = DistSigned{binbits + 5, binbits}
        t_4 = DistSigned{binbits + 8, binbits + 3}
        t_res = DistSigned{binbits + 10, binbits}

        # beta1 = add_bits(continuous(dicecontext(), p, t_g, Normal(1, 1), 0), 1, 0)
        # beta1 = continuous(dicecontext(), p, t_g, Normal(1, 1), 0)
        # beta2 = add_bits(continuous(dicecontext(), p, t_g_4, Normal(1, 1), 0), 1, 0)
        # beta2 = continuous(dicecontext(), 16*p, t_g_4, Normal(1, 1), 0)
        t = DistSigned{binbits + 4, binbits}
        t_2 = DistSigned{binbits + 7, binbits + 2}
        sigma, _ = add_bits(uniform(dicecontext(), binbits + 2, t), 0, 1) + DistSigned{binbits+5, binbits+1}(dicecontext(), 0.5)
        # sigma = discrete2(dicecontext(), [0.125, 0.25, 0.25, 0.25, 0.125], t)

        # obs = true
        # # for i = 1:1
        # i = 1
            a = continuous(dicecontext(), p, t_2, Normal(0, 1), 0)
            # term1 = Dice.trunc(a * sigma, 6)
            term1 = Dice.trunc(a*sigma, 0)
            # @show typeof(term1)
            # term2 = add_bits(beta1, 5, 0)
            # # @show typeof(term2)
            # term3 = Dice.trunc(beta2 * t(dicecontext(), y_lag[i]), 3 + binbits)
            # # @show typeof(term3)
            # temp = ((term1 + term2)[1] + term3)[1]

            # obs &= prob_equals(temp, t_res(dicecontext(), y[i]))
        # end

        # if flag == 0
        #     Cond(beta1, obs)
        # elseif flag == 1
        #     Cond(beta2, obs)
        # else
        #     Cond(sigma, obs)
        # end

        term1
        # a
        sigma
    end
    code
end


    

f = unemployment(64, 0, 0)
b = compile(f)
num_nodes(b)
num_flips(b)
a = infer(b)
c = a[63:81]
plot(map(a -> a[1], c), map(a -> a[2], c))
# KL_div(a, -8, 8, 0.125, Normal(1, 1))
# KL_div(a, -8, 8, 1, Normal(1, 1))
moment1 = expectation(b)
moment2 = variance(b)
sd = square_dist(c)
plot(sd)

abs(expectation(b) + 0.5 - 1.324379118)
variance(f, :bdd)
c = a[400:600]
plot(map(a -> a[1], c), map(a -> a[2], c))

gt_mean = [("beta[1]", 1.363409828), ("beta[2]", 0.7612146186), ("sigma", 0.928360085)]
gt_variance = [("beta[1]", 0.2140053728255653), ("beta[2]", 0.005274256728589788), ("sigma", 0.012279079516138264)]

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


function KL_div(a, lower, upper, interval, d::ContinuousUnivariateDistribution)
    d = Truncated(d, lower, upper)
    p = Vector{Float64}(undef, Int((upper - lower)/interval))
    start = lower
    count = 0
    while start < upper
        count += 1
        p[count] = cdf(d, start + interval) - cdf(d, start)
        start = start + interval
        # upper = lower + 2^F
    end
    kl_divergence(p, map(a->a[2], a))
    # @show p .- map(a->a[2], a)
    # chebyshev(p, map(a->a[2], a))
end

function square_dist(a)
    c = Dict{Float64, Float64}()
    for i=1:length(a)
        @show a[i][2]
        key = a[i][1]^2
        if key ∈ keys(c)
            c[key] = c[key] + a[i][2]
        else
            c[key] = a[i][2]
        end
    end
    c
end

flag = 0
x = Vector(undef, 200)
y = Vector(undef, 5)
for i = 4:8
    a = unemployment(2^i, 0, flag)
    b = infer(a, :bdd)
    # average = sum(map(a -> a[1]^2 * a[2], b))
    # @show average
    # @show b
    # @show KL_div(b, Normal(0, 1), 16, -16, 1)
    sd = square_dist(b[400:600])
    y[i+1 - 4] = sd
    x = map(a -> a[1]^2, b[1:513])[450:513]

    c = vcat(b[1024:-1:514], b[1024], b[1024])
    # @show c
    y[i+1 - 4] = (map(a -> a[2], b[1:513]) .+ map(a -> a[2], c))[450:513]
end
d = Normal(0, 1)
z = Vector(undef, 32)
for i=1:32
    z[i] = cdf(d, i - 16) - cdf(d, i - 17)
end
y[6] = z
plot(x, y[1:2], labels = [16 32 64 128 256])



