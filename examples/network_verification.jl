using Dice
using Dice: num_flips, num_nodes, to_dice_ir

code = @dice begin
    # network reachability example from the dice paper

    function diamond(s1)
        route = flip(0.5)
        s2 = if route s1 else false end
        s3 = if route false else s1 end
        drop = flip(0.0001)
        s2 || (s3 && !drop)
    end

    net = true
    for i=1:1
        net = diamond(net)
    end

    net
end

# BDD analysis
bdd = compile(code)
num_flips(bdd)
num_nodes(bdd)
infer(code, :bdd)

# IR analysis
to_dice_ir(code)
has_dice_binary() && rundice(code)
has_dice_binary() && infer(code, :ocaml)
# TODO FIX to not duplicate flips