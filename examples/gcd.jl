using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir


code = @dice begin
    function uniform(b::Int) # b is the bits for uniform, w is the bitwidth
        x = Vector(undef, b)
        for i = b:-1:1
            x[i] = flip(0.5)
        end
        return DistInt(x)
    end

    function GCD(a, b)
        ap = a
        bp = b
        while prob_equals(a, b)
            ap = if ap > bp 
                    (ap - bp)[1] else ap end
            bp = if !(ap > bp) bp else (bp - ap)[1] end
        end
        return ap
    end

    a = (add_bits(uniform(2), 1) + 1)[1]
    b = (add_bits(uniform(2), 1) + 1)[1]
    GCD(a, b)
        


end

bdd = compile(code)
num_flips(bdd)
num_nodes(bdd)
infer(code, :bdd)