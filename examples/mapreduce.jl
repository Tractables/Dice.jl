using Dice
using Dice: num_flips, num_nodes, to_dice_ir

res = @dice begin
    # all tails
    probs = [1/i for i=2:20]
    mapreduce(p -> !flip(p), &, probs)    
end

# BDD analysis
num_flips(res)
num_nodes(res)
infer_bool(res)

# IR analysis
# println(to_dice_ir(code))
# has_dice_binary() && rundice(code)
# has_dice_binary() && infer(code, :ocaml)
