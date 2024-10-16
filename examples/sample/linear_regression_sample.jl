using Revise
using Dice
using Random
using Distributions

# Ground truth calculation
nobs = 1
true_w1 = 1
true_w2 = 2

x1s = rand(Uniform(-2, 2), nobs)
x2s = rand(Uniform(-2, 2), nobs)
error = rand(Normal(0, 1), nobs)
y1s = true_w1.*x1s + true_w2.*x2s + error

X = hcat(x1s, x2s)
S = hcat([2, 0], [0, 2])
sigma = inv(transpose(X) * X + inv(S))
mu = sigma * transpose(transpose(y1s) * X)
println("Ground truth")
@show mu

# Normal Dice program
bits = 2
pieces = 2^(bits+4)
DFiP = DistFix{6 + bits, bits}

code = @dice begin
        w1 = bitblast(DFiP, Normal(0, sqrt(2)), pieces, -8.0, 8.0)
        w2 = bitblast(DFiP, Normal(0, sqrt(2)), pieces, -8.0, 8.0)
            for i in 1:nobs
                error = bitblast(DFiP, Normal(0, 1), pieces, -8.0, 8.0)
                observe(prob_equals(DFiP(y1s[i]), DFiP(x1s[1])*w1 + DFiP(x2s[1])*w2 + error) )           
            end
        w2
end
p = pr(code)
e = expectation(code)
println("Expectation from true Dice program")
@show e


NSAMPLES=1000
samples = rand(Bernoulli(0.5), NSAMPLES, 4)
samples = map(x -> if x == 1 true else false end, samples)

function dice_program(s)
    code = @dice begin
        w1 = bitblast(DFiP, Normal(0, sqrt(2)), pieces, -8.0, 8.0)
        w2 = bitblast(DFiP, Normal(0, sqrt(2)), pieces, -8.0, 8.0)
        observe(prob_equals(w1.mantissa.number.bits[5+bits:6+bits], s[1:2]))
        observe(prob_equals(w2.mantissa.number.bits[5+bits:6+bits], s[3:4]))
        for i in 1:nobs
            error = bitblast(DFiP, Normal(0, 1), pieces, -8.0, 8.0)
            observe(prob_equals(DFiP(y1s[i]), DFiP(x1s[1])*w1 + DFiP(x2s[1])*w2 + error) )           
        end
        w2
    end
    inside_expectation = expectation(code)
    prob_evidence = pr(allobservations(code))
    # @show prob_evidence
    return inside_expectation, prob_evidence[true]
end


mean = mapslices(x -> dice_program(x), samples;dims=2)

num = sum(map(x -> x[1]*x[2]/0.0625, mean))
den = sum(map(x -> x[2]/0.0625, mean))
sampled_expectation = num/den
println("Last two bits sampled")
@show sampled_expectation