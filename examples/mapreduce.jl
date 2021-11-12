using Dice
using Dice: num_flips, num_nodes, to_dice_ir

code = @dice begin
    # all tails
    probs = [1/i for i=2:20]
    mapreduce(p -> !flip(p), &, probs)    
end

# BDD analysis
bdd = compile(code)
println("Number of flips used: $(num_flips(bdd))")
println("Number of BDD nodes: $(num_nodes(bdd))")

# IR analysis
println(to_dice_ir(code))
has_dice_binary() && rundice(code)
has_dice_binary() && infer(code, :ocaml)
