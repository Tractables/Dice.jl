using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir
using Distributions
using StatsBase
using Distances
using Plots

function anova_radon_nopred(p::Int, binbits::Int, flag::Int)
    
    code = @dice begin
        precision = 3

        data = [0.617007250574049]
        # data = [-0.67]

        t_s = DistSigned{binbits + 5 + precision, binbits + precision}
        t_g = DistSigned{binbits + 4 + precision, binbits + precision}
        t_a1 = DistSigned{binbits + 9, binbits}

        #constructing a1
        a11 = uniform(dicecontext(), binbits + 3, t_a1)
        a12 = if flip(1/2) a11 else (a11 + t_a1(dicecontext(), 1/2^binbits))[1] end
        a1, _ = a12 - t_a1(dicecontext(), 4.0) # -4 to 4

        #constructing sigmay
        sigmay1 = uniform(dicecontext(), binbits + 2 + precision, t_s)
        sigmay = if flip(1/2) sigmay1 else (sigmay1 + t_s(dicecontext(), 1/2^(binbits + precision)))[1] end
        
        obs = true
        i = 1
        y = continuous(dicecontext(), p, t_g, Normal(0, 1), 0, 1)
        y = Dice.trunc(y * sigmay, 2*precision + binbits)
        y, _ = y + a1
        obs &= prob_equals(y, t_a1(dicecontext(), data[i]))

        if flag == 0
            Cond(a1, obs)
        else
            Cond(sigmay, obs)
        end
        # t_a1(dicecontext(), data[1])
        
        
    end
    code
end


f = anova_radon_nopred(64, 1, 0)
a = compile(f)
num_flips(a)
num_nodes(a)
b = infer(a)
c = b
plot(map(a -> a[1], c), map(a -> a[2], c))
expectation(a)
variance(a)