using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir

code = @dice begin

    
    function uniform(b::Int, t::Type) # b is the bits for uniform, w is the bitwidth
        x = Vector(undef, b)
        for i = b:-1:1
            x[i] = flip(0.5)
        end
        return t(x)
    end
    sum = uniform(2, DistFixParam{1})
    sum2 = uniform(2, DistFixParam{2})
    println(typeof(sum + sum))
end

# BDD analysis
bdd = compile(code)
# num_flips(bdd)
# num_nodes(bdd)
infer(code, :bdd)