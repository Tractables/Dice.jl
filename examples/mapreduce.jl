using Dice
using Dice: num_flips, num_nodes

alltails = @dice_bdd begin
    probs = [1/i for i=2:20]
    mapreduce(p -> !flip(p), &, probs)    
end

println("Number of flips used: $(num_flips(alltails))")
println("Number of BDD nodes: $(num_nodes(alltails))")

@dice_ir begin
    probs = [1/i for i=2:20]
    mapreduce(p -> !flip(p), &, probs)    
end

if has_dice_binary()
    @dice_run begin
        probs = [1/i for i=2:20]
        mapreduce(p -> !flip(p), &, probs)    
    end
end