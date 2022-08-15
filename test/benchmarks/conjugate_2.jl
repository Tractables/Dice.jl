using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir
using Distributions
using StatsBase
using Distances
using Plots

function conjugate_2(p::Int, bits::Int)
    code = @dice begin
        helper(a::Float64) = if a <= 0 10^(-11) else a^2 end
        helper2(a::Float64) = a

        # t = DistFixParam{bits + 5, bits}
        t = DistSigned{bits + 3, bits}

        sigma = continuous(dicecontext(), p, t, InverseGamma(3, 2), 0, 0, helper)
        
        # data = [1.0, 3.0]

        # obs = true
        # for i=1:length(data)
        #     y = continuous(dicecontext(), p, t, Normal(0, 1), 0, 0, helper2) * sigma
        #     obs &= prob_equals(y, t(dicecontext(), data[i]))

        # #     # y = continuous(dicecontext(), p, t, Normal(data[i], sqrt(2)), 0, 0)
        # #     # obs &= prob_equals(y, mu)
        # end

        # Cond(sigma, obs)
        sigma
        # mu
        # y
    end
    code
end

a = conjugate_2(256, 6)
b = compile(a)
num_nodes(b)
num_flips(b)
c = infer(b)
plot(map(a -> a[1], c), map(a -> a[2], c))
d = expectation(b)
e = variance(b)