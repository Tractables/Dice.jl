using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir
using Distributions
using StatsBase
using Distances
using Plots

function zeroone(binbits::Int, flag::Int)
    code = @dice begin
        y = [1, -1, 1, -1, -1, -1, 1, 1, 1, 1, 1, -1, 1, -1, -1, -1, 1, 1, 1, 1]
        
        x1 = [6, 8, -1, 0, 5, 1.2, -2, 9.8, 4, 12, 1, 10, 1, 2.2, -6, 9.8, 1, 1, 1, 1]

        t = DistSigned{binbits + 5, binbits}
        t_4 = DistSigned{binbits + 9, binbits + 4}
        t_res = DistSigned{2*binbits + 10, 2*binbits}

        w1, _ = uniform(dicecontext(), binbits + 4 + 4, t_4) - t_4(dicecontext(), 8.0)
        w2, _ = uniform(dicecontext(), 2*binbits + 4, t_res) - t_res(dicecontext(), 8.0)

        obs = true

        for i=1:20
            term1 = w1 * t(dicecontext(), x1[i])
            term1 = Dice.trunc(term1, 4)
            term2 = w2
            temp, _ = term1 + term2
            if y[i] == 1
                obs &= !isneg(temp) || (isneg(temp) & flip(1/ℯ))
            else
                obs &= isneg(temp) || (!isneg(temp) & flip(1/ℯ))
            end
        end

        if flag == 0
            Cond(w1, obs)
        else
            Cond(w2, obs)
        end
        # Dice.trunc(w1, 4)
        # temp
    end
end

f = zeroone(1, 0)
b = compile(f)
num_nodes(b)
num_flips(b)
c = infer(b)
sum(map(a -> a[2], c))
d = c[2000:2100]
plot(map(a -> a[1], d), map(a -> a[2], d))