using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir
using Distributions
using StatsBase
using Distances
using Plots

function conjugate_1(p::Int, bits::Int)
    code = @dice begin
        t = DistSigned{bits + 5, bits}

        mu = continuous(dicecontext(), p, t, Normal(1, sqrt(5)), 0, 0)
        
        data = [9.0, 8.0, 9.0, 8.0]

        obs = true
        for i=1:length(data)
            y, _ = continuous(dicecontext(), p, t, Normal(0, sqrt(2)), 0, 0) + mu
            obs &= prob_equals(y, t(dicecontext(), data[i]))

            # y = continuous(dicecontext(), p, t, Normal(data[i], sqrt(2)), 0, 0)
            # obs &= prob_equals(y, mu)
        end

        Cond(mu, obs)
        # mu
        # y
    end
    code
end

a = conjugate_1(256, 5)
b = compile(a)
num_nodes(b)
num_flips(b)
c = infer(b)
plot(map(a -> a[1], c), map(a -> a[2], c))
d = expectation(b)
e = variance(b)