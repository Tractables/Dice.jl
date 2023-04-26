using Revise
using Dice, Distributions
using DelimitedFiles
using BenchmarkTools
using Plots
using JLD

bits = parse(Int64, ARGS[1])
flag = parse(Int64, ARGS[3])

bits = 8
flag = 1

p = pr(@dice uniform(DistUInt{3}))

DFiP = DistFixedPoint{8+bits, bits}

ys = [1, -1, 1, -1, -1, -1, 1, 1, 1, 1, 1, -1, 1, -1, -1, -1, 1, 1, 1, 1]
xs = DFiP.([6, 8, -1, 0, 5, 1.2, -2, 9.8, 4, 12, 1, 10, 1, 2.2, -6, 9.8, 1, 1, 1, 1])

t = @dice begin
            w1 = uniform(DFiP, -8.0, 8.0)
            w2 = uniform(DFiP, -8.0, 8.0)

            for (x, y) in zip(xs, ys)
                temp = x*w1 + w2
                isneg = temp < DFiP(0.0)
                if y == 1
                    observe(!isneg | (isneg & flip(1/ℯ)))
                else
                    observe(isneg | (!isneg & flip(1/ℯ)))
                end
            end
            if flag == 1
                w1
            else
                w2
            end
        end

function cdf_from_p(pr, i::Float64)
    sum = 0
    for (k, v) in pr
        if k <= i
            sum = sum + v
        end
    end
    sum
end


p = pr(t)
ans_vector = Vector(undef, 100)
cdf_sum = 0
count = 0
for i in range(-8, 8, 100)
    @show i, count, floor(i*2^8)/2^8
    count = count+1
    cdf_sum += p[floor(i*2^8)/2^8]
    # cdf_from_p(p, i)
    ans_vector[count] = cdf_from_p(p, i)
    @show cdf_sum
end

plot(p)
plot(ans_vector)


# reading bit latte

d = load("./bit-latte/zeroone/flag_1.jld")
bit_latte_expec = Vector(undef, 100)
for i in 1:100
    bit_latte_expec[i] = d["expect"][i]*ans_vector[i]
end
plot!(bit_latte_expec)

# reading ground truth
gt = [0., 0.000959838, 0.0029154, 0.00586668, 0.00981369, 0.0147564, 0.0206949, 0.0276291, 0.035559, 0.0443156, 0.0533498, 0.0626193,
0.0721241, 0.0818641, 0.0918395, 0.10205, 0.112496, 0.123177, 0.134094, 0.145246, 0.156633, 0.168256, 0.180113, 0.192206, 0.204535,
0.217098, 0.229896, 0.242925, 0.256051, 0.268916, 0.2815, 0.293803, 0.305825, 0.317567, 0.329028, 0.340208, 0.351107, 0.361726, 0.372181,
0.383171, 0.394812, 0.406523, 0.417798, 0.429654, 0.442347, 0.454593, 0.465454, 0.475159, 0.484064, 0.492171, 0.499478, 0.506877, 0.515257,
0.524619, 0.534963, 0.546271, 0.558531, 0.571768, 0.585991, 0.600886, 0.615437, 0.62957, 0.643288, 0.656591, 0.669474, 0.681936, 0.693977,
0.705597, 0.716797, 0.727575, 0.737933, 0.74787, 0.757386, 0.766482, 0.775159, 0.783419, 0.791495, 0.79962, 0.807793, 0.816015, 0.824287,
0.832607, 0.840976, 0.849394, 0.85786, 0.866376, 0.87494, 0.883554, 0.892216, 0.900927, 0.909687, 0.918496, 0.927354, 0.936261, 0.945218,
0.954224, 0.96328, 0.972386, 0.981541, 0.990746]
plot!(gt)

for i in 1:100
    if ans_vector[i] < gt[i]
        @show i
    end
end

true_bit_latte_expec = Vector(undef, 100)
for i in 1:100
    true_bit_latte_expec[i] = gt[i]/ans_vector[i]
end

plot(map(a -> log(a), ans_vector))
plot!(map(a -> log(a), gt))
plot!(map(a -> log(a), bit_latte_expec))

f(a, b) = abs(a - b)

plot(map(f, ans_vector, gt), label="hybit")
plot!(map(f, bit_latte_expec, gt), label="bit-latte")
savefig("zeroone.png")

p = t.value
io = open(string("./bit-latte/zeroone/results.txt"), "a")
readlm(io)

io = open(string("./bit-latte/zeroone/results.txt"), "a")
@show bits, p, flag, t.time
writedlm(io, [bits p flag t.time], ",")  
close(io)