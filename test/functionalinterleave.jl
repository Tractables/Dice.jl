using Pkg; Pkg.activate(@__DIR__);

using Dice: @dice, num_flips, num_nodes

@dice begin
    
    probs = [1/i for i=2:20]

    alltails = mapreduce(p -> !flip(p), &, probs)

    println("Number of flips used: $(num_flips(alltails))")
    println("Number of BDD nodes: $(num_nodes(alltails))")

end