using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir
using Distributions

code = @dice begin
        
    function uniform(b::Int, point::Int)
        x = Vector(undef, b)
        for i = b:-1:1
            x[i] = flip(0.5)
        end
        return DistFix(DistInt(x), point)
    end

    function triangle(b::Int, point::Int)
        s = false
        n = 2^b
        x = Vector(undef, b)
        y = Vector(undef, b)
        for i = b:-1:1
            x[i] = Dice.ifelse(s, flip(1/2), flip((3n - 2)/ (4n-4)))
            y[i] = flip((n-2)/(3n-2))
            s = s || (x[i] && !y[i])
            n = n/2
        end
        return DistFix(DistInt(x), point)
    end

    # function gaussian(type, mean, std, linear_pieces)

    triangle(4, 2)
end



bdd = compile(code)
num_flips(bdd)
num_nodes(bdd)
(infer(code, :bdd))
@assert infer(code, :bdd) ≈ 0.5

bdd = compile(code)
num_flips(bdd)
num_nodes(bdd)
infer(code, :bdd)