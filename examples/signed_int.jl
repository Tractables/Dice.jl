
using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir

code = @dice begin 
        a = DistSigned{2, 0}(dicecontext(), -2.0)
        prob_equals(a, DistSigned{2, 0}(dicecontext(), 1.0))
    end

infer(code, :bdd)
