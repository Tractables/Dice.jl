using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir
using Distributions

code = @dice begin
        
    f1 = flip(0.5)
    # f2 = flip(0.5)
    aa = DistInt([f1, flip(0.5)])
    # bb = DistInt([f1, flip(1), flip(0)])
    a = DistSignedInt(aa)
    # b = DistSignedInt(bb)

    # prob_equals(a, b)
    a
end



bdd = compile(code)
(infer(code, :bdd))
# @assert infer(code, :bdd) ≈ 0.5

bdd = compile(code)
num_flips(bdd)
num_nodes(bdd)
infer(code, :bdd)