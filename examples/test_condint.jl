using Dice
using Dice: num_flips, num_nodes

cg = @dice begin
    function uniform(b::Int)
        a = b/2
        d = true
        bits = Vector(undef, b)
        for i=1:b
            rep = flip(0.5)
            bits[i] = rep
            if i > a
                d &= rep
            else
                d &= true
            end
        end
        return DistInt(bits), d
    end

    a, b = uniform(4)
    CondInt(a, b)
end

# BDD analysis
# bdd = compile(code)
infer(cg)

# IR analysis
# to_dice_ir(code)
# has_dice_binary() && rundice(code)
# has_dice_binary() && infer(code, :ocaml)