using Dice
using Dice: num_flips, num_nodes

bdd = @dice_bdd begin
    # network reachability example from the dice paper

    function diamond(s1)
        route = flip(0.5)
        s2 = if route s1 else false end
        s3 = if route false else s1 end
        drop = flip(0.0001)
        s2 || (s3 && !drop)
    end

    net = true
    for i=1:3
        net = diamond(net)
    end

    net
end

println("Number of flips used: $(num_flips(bdd))")
println("Number of BDD nodes: $(num_nodes(bdd))")
