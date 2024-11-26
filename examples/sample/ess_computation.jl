# A self contained file to compute effective sample size of different bits in a model.

using Revise
using Dice
using Random
using Distributions
using LinearAlgebra
using DelimitedFiles

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
bits = 2
pieces = 2^(bits+4)
DFiP = DistFix{7 + bits, bits}

code = @dice begin
        ws = [bitblast(DFiP, Normal(0, sqrt(2)), pieces, -8.0, 8.0) for i in 1:10]
        for i in 1:nobs
            error = bitblast(DFiP, Normal(0, 1), pieces, -8.0, 8.0)
            linear = reduce(+, map(*, DFiP.(xs), ws))
            observe(prob_equals(linear + error, DFiP(ys[i])))        
        end
        ws[2]
end
# p = pr(code)
e = expectation(code)
println("Expectation from true Dice program")
@show e

function ess(weights)
    Z = sum(weights)
    normalized_weights = weights/Z
    squared_weights = sum(map(x -> x^2, normalized_weights))
    1/squared_weights
end 


NSAMPLES=1000
samples = rand(Bernoulli(0.5), NSAMPLES)
samples = map(x -> if x == 1 true else false end, samples)

function dice_program(s, bit, gauss)
    # @show gauss, bit, s
    code = @dice begin
        gauss_vector = [bitblast(DFiP, Normal(0, sqrt(2)), pieces, -8.0, 8.0) for j in 1:3]
        w1 = gauss_vector[1]
        w2 = gauss_vector[2]
        observe(prob_equals(gauss_vector[gauss].mantissa.number.bits[bit], s))
        for i in 1:nobs
            error = gauss_vector[i+2]
            observe(prob_equals(DFiP(ys[i]), DFiP(xs[i, 1])*w1 + DFiP(xs[i, 2])*w2 + error) )               
        end
        w2
    end
    inside_expectation = expectation(code)
    prob_evidence = pr(allobservations(code))
    # @show prob_evidence
    return inside_expectation, prob_evidence[true]
end

# Data points - gauss, bit, error from the true answer, error from the Dice answer, ess

for i in 1:3
    for j in 1:bits+6
        p = @timed mean = map(x -> dice_program(x, j, i), samples)
        num = sum(map(x -> x[1]*x[2]/0.5, mean))
        weights = map(x -> x[2]/0.5, mean)
        den = sum(weights)

        sampled_expectation = num/den
        sample_size = ess(weights)

        io = open(string("ess.txt"), "a")
        @show i, j, abs(sampled_expectation - mu[2]), abs(sampled_expectation - e), sample_size, p.time
        writedlm(io, [i j abs(sampled_expectation - mu[2]) abs(sampled_expectation - e) sample_size p.time], ",")  
        close(io)
    end
end

