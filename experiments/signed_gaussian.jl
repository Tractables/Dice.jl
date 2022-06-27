using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir
using Distributions

code = @dice begin

    # a = continuous(dicecontext(), 16, DistFixParam{5, 0}, Normal(16, 4))
    a = DistSigned{2, 0}(dicecontext(), -1.0) - DistSigned{2, 0}(dicecontext(), 1.0)

    a[1]
end

# BDD analysis
bdd = compile(code)
num_flips(bdd), num_nodes(bdd)
infer(code, :bdd)