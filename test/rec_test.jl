using Dice
using Dice: num_flips, num_nodes, to_dice_ir

code = @dice begin
    function test_rec(a::Int)
        ans = if a <= 0
                    flip(0.5)
        else
            flip(0.5) & test_rec(a - 1)
        end
    end

    test_rec(2)
end



bdd = compile(code)
num_flips(bdd)
num_nodes(bdd)
@assert infer(code, :bdd) ≈ 0.125