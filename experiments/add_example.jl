using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir

code = @dice begin

    function uniform(bitrange::Int, bitwidth::Int)
        ans = fill(DistBool(dicecontext(), false), bitwidth)
        for i = 1:bitrange
            ans[i] = flip(0.5)
        end
        DistInt(ans)
    end

    a = uniform(2, 3)
    b = uniform(2, 3)
    c, _ = (a+b)
    c
end

# BDD analysis
bdd = compile(code)
num_flips(bdd), num_nodes(bdd)
infer(code, :bdd)