using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir
using Distributions
using StatsBase
using Distances

function zeroone(binbits::Int)
    code = @dice begin
        y = [1, -1, 1, -1, -1, -1, 1, 1, 1, 1, 1, -1, 1, -1, -1, -1, 1, 1, 1, 1]
        
        # x1 [-6, 10]
        x1 = [6, 8, -1, 0, 5, 1.2, -2, 9.8, 4, 12,
        1, 10, 1, 2.2, -6, 9.8, 1, 1, 1, 1]

        t = DistSigned{binbits + 5, binbits}
        t_4 = DistSigned{binbits + 9, binbits + 4}
        t_res = DistSigned{2*binbits + 10, binbits}

        # additional precision 4, adding bits (binbits + 5, 0)
        w1 = add_bits((uniform(dicecontext(), binbits + 8, t_4) - t_4(dicecontext(), 8.0))[1], binbits + 5, 0)
        w2 = (uniform(dicecontext(), binbits + 4, t) - t(dicecontext(), 8.0))[1]

        obs = true
        for i = 1:3

            term1 = t_res((t(dicecontext(), x[i]).number * w1.number)[1].bits[5:2*binbits + 14])
            term2 = add_bits(w2, binbits + 5, 0)

            temp = (term1 + term2)[1]

            if y[i] == 1
                print(1)
                obs &= !isneg(temp)
            else
                print(2)
                obs &= isneg(temp)
            end

        end
        obs
    end
    code
end

f = zeroone(1)
b = compile(f)
num_nodes(b)
num_flips(b)
a = infer(f, :bdd)
expectation(f, :bdd)
variance(f, :bdd)