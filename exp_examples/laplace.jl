using Revise
using Dice
using Plots

f(i, beta) = exp(beta/2^i)/ (1 + exp(beta/2^i))

function laplace_bits(b::Int, mu::Float64, sigma::Float64)

    DFiP = DistFixedPoint{b + 3, b}

    beta1 = -1/sigma
    a_vec = vcat([false, false, false], [flip(f(i, beta1)) for i in 1:b])
    a = DFiP(a_vec) + DFiP(mu)

    beta2 = 1/sigma
    c_vec = vcat([false, false, false], [flip(f(i, beta2)) for i in 1:b])
    c = DFiP(c_vec) + DFiP(mu - 1.0)

    d = ifelse(flip(0.5), a, c)
    d
end

a = laplace_bits(14, 0.0, 0.0025)
b = laplace_bits(14, 1.0, 0.0025)
d = ifelse(flip(0.5), a, b)

expectation(d) + 1/2^15
plot(pr(d))