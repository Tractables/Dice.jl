using Pkg; Pkg.activate(@__DIR__);

using Dice: @dice, num_flips, num_nodes, @dice_ir

alltails = @dice :bdd begin
    probs = [1/i for i=2:20]
    mapreduce(p -> !flip(p), &, probs)    
end

println("Number of flips used: $(num_flips(alltails))")
println("Number of BDD nodes: $(num_nodes(alltails))")

@dice_ir begin
    probs = [1/i for i=2:20]
    mapreduce(p -> !flip(p), &, probs)    
end