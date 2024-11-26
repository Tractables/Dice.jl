using Dice
using Distributions
using Test

x1s = -1.359
x2s = -0.458
error1 = -2.25
y1s = x1s + 2*x2s + error1

X = hcat(x1s, x2s)
S = hcat([2, 0], [0, 2])
sigma = inv(transpose(X) * X + inv(S))
mu = sigma * transpose(transpose(y1s) * X)

bits = 7
pieces = 2^(8)
DFiP = DistFix{9+bits, bits}

w1 = bitblast(DFiP, Normal(0, sqrt(2)), pieces, -8.0, 8.0)
w2 = bitblast(DFiP, Normal(0, sqrt(2)), pieces, -8.0, 8.0)
code = @dice begin
            error1 = bitblast(DFiP, Normal(0, 1), pieces, -8.0, 8.0)
            observe(prob_equals(DFiP(y1s[1]), DFiP(x1s[1])*w1 + DFiP(x2s[1])*w2 + error1))
            w1
end

@test isapprox(expectation(code), mu[1]; atol = 0.1)