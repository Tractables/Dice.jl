using Revise
using Dice
using Random
using Distributions
using LinearAlgebra

bits = 3
pieces = 2^(bits+2)
DFiP = DistFix{5 + bits, bits}
DFiP2 = DistFix{5 + bits - 2, bits - 2}

xs = rand(Uniform(-2, 2))
e = rand(Normal(0, 1))
ys = xs + e
# true_w = 1

# Below is an example where sampling from error bits can lead to a contradiction
code = @dice begin
        x1 = DFiP([false, false, false, false, true, true, false, false])
        x2 = DFiP([false, false, false, false, false, true, false, false])
        w = DFiP([false, false, false, flip(0.5), flip(0.5), flip(0.5), flip(0.5), false])

        e1 = DFiP([false, false, false, flip(0.5), flip(0.5), flip(0.5), flip(0.5), false])
        e2 = DFiP([false, false, false, flip(0.5), flip(0.5), flip(0.5), flip(0.5), true])
        # observe(prob_equals(w*x1, e1))
        observe(prob_equals(w*x2, e2))
        w
end

pr(code)
# include("../../src/dist/bool.jl")
# returnvalue(code).mantissa.number.bits[7]
