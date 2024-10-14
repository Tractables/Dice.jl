using Dice
using Revise
using Distributions
using DelimitedFiles

nobs = 5
true_w1 = 0
true_w2 = 2

x1s = rand(Uniform(-2, 2), nobs)
x2s = rand(Uniform(-2, 2), nobs)
error = rand(Normal(0, 1), nobs)
y1s = true_w1.*x1s + true_w2.*x2s + error

X = hcat(x1s, x2s)
S = hcat([2, 0], [0, 2])
sigma = inv(transpose(X) * X + inv(S))
mu = sigma * transpose(transpose(y1s) * X)


for bits in 1:20
    pieces = 2^(bits + 4)
    DFiP = DistFix{9+bits, bits}

    w1 = bitblast(DFiP, Normal(0, 2), pieces, -8.0, 8.0)
    w2 = bitblast(DFiP, Normal(0, 2), pieces, -8.0, 8.0)
    code = @dice begin
               for i in 1:nobs
                    error = bitblast(DFiP, Normal(0, 1), pieces, -8.0, 8.0)
                   observe(prob_equals(DFiP(y1s[i]), DFiP(x1s[i])*w1 + DFiP(x2s[i])*w2 + error) )           
               end
            w2
    end
    p = @timed expectation(code, ignore_errors=true)
    io = open(string("bits_linear_regression.txt"), "a")
    writedlm(io, [p.value-mu[2] p.time], ',')
    close(io)
end