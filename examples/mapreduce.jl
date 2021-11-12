using Dice
using Dice: num_flips, num_nodes, to_dice_ir

code = @dice begin
    # all tails
    probs = [1/i for i=2:20]
    mapreduce(p -> !flip(p), &, probs)    
end

# BDD analysis
bdd = compile(code)
num_flips(bdd)
num_nodes(bdd)
infer(code, :bdd)

# IR analysis
println(to_dice_ir(code))
has_dice_binary() && rundice(code)
has_dice_binary() && infer(code, :ocaml)
