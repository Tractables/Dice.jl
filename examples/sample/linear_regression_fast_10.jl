using Revise
using Dice
using Random
using Distributions
using LinearAlgebra

# Ground truth calculation
nobs = 1
nweights = 2

true_w = [1 for i in 1:nweights]

xs = rand(Uniform(-2, 2), nobs, nweights)
error = rand(Normal(0, 1), nobs)
ys = reduce(+, map(*, xs, true_w)) + error[1]

X = xs
S = Diagonal([2 for i in 1:nweights])
sigma = inv(transpose(X) * X + inv(S))
mu = sigma * transpose(transpose(ys) * X)
println("Ground truth")
@show mu

# Normal Dice program
bits = 4
pieces = 2^(bits+4)
DFiP = DistFix{9 + bits, bits}

code = @dice begin
        ws = [bitblast(DFiP, Normal(0, sqrt(2)), pieces, -8.0, 8.0) for i in 1:10]
        # w2 = bitblast(DFiP, Normal(0, sqrt(2)), pieces, -8.0, 8.0)
        for i in 1:nobs
            error = bitblast(DFiP, Normal(0, 1), pieces, -8.0, 8.0)
            linear = reduce(+, map(*, DFiP.(xs), ws))
            observe(prob_equals(linear + error, DFiP(ys[i])))
            # observe(prob_equals(DFiP(y1s[i]), DFiP(x1s[1])*w1 + DFiP(x2s[1])*w2 + error) )           
        end
        ws[2]
end
# p = pr(code)
e = expectation(code)
println("Expectation from true Dice program")
@show e


NSAMPLES=1000
samples = rand(Bernoulli(0.5), NSAMPLES, 6)
samples = map(x -> if x == 1 true else false end, samples)


function gaussian_sample(s, std)
    param = s[1]*0.5 + s[2]*0.25
    w1 = bitblast_sample(DistFix{7+bits, 0}, Normal(0, std), pieces, -8.0, 8.0, param, 0.25)
    DFiP([w1.mantissa.number.bits..., s[1], s[2]])
end

bits = 2
pieces = 2^(bits+1)
DFiP = DistFix{9 + bits, bits}


function dice_program(s)
    code = @dice begin
        w1 = gaussian_sample(s[1:2], sqrt(2))
        w2 = gaussian_sample(s[3:4], sqrt(2))
        # w1 = bitblast_sample(DistFix{4+bits, 0}, Normal(0, sqrt(2)), pieces, -8.0, 8.0, param1, 0.25)
        # w2 = bitblast_sample(DistFix{4+bits, 0}, Normal(0, sqrt(2)), pieces, -8.0, 8.0, param2, 0.25)
        # # observe(prob_equals(w1.mantissa.number.bits[5+bits:6+bits], s[1:2]))
        # # observe(prob_equals(w2.mantissa.number.bits[5+bits:6+bits], s[3:4]))
        # w1 = DFiP([w1.mantissa.number.bits..., s[1], s[2]])
        # w2 = DFiP([w2.mantissa.number.bits..., s[3], s[4]])
        for i in 1:nobs
            # error = gaussian_sample(s[5:6], 1)
            error = bitblast(DistFix{9+bits, bits}, Normal(0, 1), pieces, -8.0, 8.0)
            observe(prob_equals(DFiP(ys[i]), DFiP(xs[1])*w1 + DFiP(xs[1])*w2 + error) )           
        end
        w2
    end
    inside_expectation = expectation(code)
    prob_evidence = pr(allobservations(code))
    # @show prob_evidence
    return inside_expectation, prob_evidence[true]
end


pfast = @timed mean = mapslices(x -> dice_program(x), samples;dims=2)

num = sum(map(x -> x[1]*x[2]/0.0625, mean))
den = sum(map(x -> x[2]/0.0625, mean))
sampled_expectation = num/den
println("Last two bits sampled")
@show sampled_expectation