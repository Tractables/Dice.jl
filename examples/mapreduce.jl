using Dice
using Dice: num_flips, num_nodes, to_dice_ir

alltails = @dice begin
    probs = [1/i for i=2:20]
    mapreduce(p -> !flip(p), &, probs)    
end

bdd = compile(alltails)
println("Number of flips used: $(num_flips(bdd))")
println("Number of BDD nodes: $(num_nodes(bdd))")

ir = to_dice_ir(alltails)
println(ir)
has_dice_binary() && rundice(ir)
has_dice_binary() && rundice(alltails)
