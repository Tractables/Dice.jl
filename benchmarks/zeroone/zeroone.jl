using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir
using Distributions
using StatsBase
using Distances

function zeroone(binbits::Int)
    code = @dice begin
        y = [1, -1, 1, -1, -1, -1, 1, 1, 1, 1, 1, -1, 1, -1, -1, -1, 1, 1, 1, 1]
        
        x1 = [6, 8, -1, 0, 5, 1.2, -2, 9.8, 4, 12, 1, 10, 1, 2.2, -6, 9.8, 1, 1, 1, 1]

        t = DistSigned{binbits + 5, binbits}
        t_4 = DistSigned{binbits + 9, binbits + 4}
        t_res = DistSigned{2*binbits + 8, binbits}

        # additional precision 4, adding bits (binbits + 5, 0)
        w1_og = (uniform(dicecontext(), binbits + 8, t_4) - t_4(dicecontext(), 8.0))[1]
        # w1_og = t_4(dicecontext(), 8.0)
        w1 = add_bits(w1_og, binbits + 5, 0)
        w2 = (uniform(dicecontext(), binbits + 4, t) - t(dicecontext(), 8.0))[1]

        obs = true
        # for i = 1:20
        i = 2
            term1 = t_res((w1.number * t(dicecontext(), x1[i]).number)[1].bits[9:2*binbits + 10])
            term2 = add_bits(w2, binbits + 3, 0)

            temp = (term1 + term2)[1]

            # if y[i] == 1
                # obs &= !isneg(temp) || (isneg(temp) & flip(1/ℯ))
            # else
                # obs &= isneg(temp) || (!isneg(temp) & flip(1/ℯ))
            # end

        # end
        # Cond(w1_og, obs)
        term1
        # w2
        # obs
        # a
    end
    code
end

f = zeroone(5)
b = compile(f)
num_nodes(b)
num_flips(b)
a = infer(f, :bdd)
expectation(f, :bdd)
variance(f, :bdd)
c = a
for i in a
    if i[1] == -64
        print(i)
    end
end
plot(map(a -> a[1], c), map(a -> a[2], c))
