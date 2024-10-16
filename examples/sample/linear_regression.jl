using Revise
using Dice
using Distributions
using DelimitedFiles

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

bits = 6
for bits in 1:7
    pieces = 2^(bits + 4)
    DFiP = DistFix{9+bits, bits}

    w1 = bitblast(DFiP, Normal(0, sqrt(2)), pieces, -16.0, 16.0)
    w2 = bitblast(DFiP, Normal(0, sqrt(2)), pieces, -16.0, 16.0)
    code = @dice begin
               for i in 1:nobs
                    error = bitblast(DFiP, Normal(0, 1), pieces, -8.0, 8.0)
                   observe(prob_equals(DFiP(y1s[i]), DFiP(x1s[1])*w1 + DFiP(x2s[1])*w2 + error) )           
               end
            w2
    end
    p = pr(code)
    p = @timed expectation(code)
    io = open(string("bits_linear_regression.txt"), "a")
    writedlm(io, [bits p.value-mu[2] p.time], ',')
    close(io)
end
