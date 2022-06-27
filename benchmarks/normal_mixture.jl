using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir
using BenchmarkTools
using DelimitedFiles

code = @dice begin 
            mu1 = continuous(8, DistFixParam{5, 2}, Normal(15, 1))
            mu2 = continuous(8, DistFixParam{5, 2}, Normal(5, 1))
            theta = uniform(DistFixParam{5, 2}, 2)

            d = (if flip(theta) 
                    continuous(8, DistFixParam{5, 2}, Normal(10, 1)) + mu1
                else
                    continuous(8, DistFixParam{5, 2}, Normal(10, 1)) + mu2
                end)[1]

            obs = true
            obs &= prob_equals(d, DistFixParam{5, 2}(dicecontext(), 10))

            Cond()
        end



