using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir
using Distributions
using StatsBase
using Distances
    
code = @dice begin
        a = add_bits(DistSigned{3, 2}(dicecontext(), -1.0), 1, 0)
        b = add_bits(DistSigned{3, 2}(dicecontext(), -1.0), 1, 0)
        (a+b)[1]
end

a = compile(code)
b = infer(a)