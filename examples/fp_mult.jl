using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir

code = @dice begin

    a = uniform(dicecontext(), 3, DistFixParam{3, 3})
    b = uniform(dicecontext(), 3, DistFixParam{3, 3})

    # a
    DistFixParam{3, 3}((a*b)[1])
    # (a*b)[1]
end

# BDD analysis
# bdd = compile(code)
# num_flips(bdd), num_nodes(bdd)
# infer(code, :bdd)

infer(code, :bdd)