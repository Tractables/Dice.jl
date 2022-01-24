using Dice
using Dice: num_flips, num_nodes, to_dice_ir

function code_div(b1::Int, b2::Int, res::Int)
    code = @dice begin
        function uniform(b::Int, w::Int) # b is the bits for uniform, w is the bitwidth
            x = Vector(undef, b)
            for i = b:-1:1
                x[i] = flip(0.5)
            end
            return add_bits(ProbInt(x), w - b)
        end
        a = (uniform(b1, b1+1) + 1)[1]
        b = (uniform(b2, b2+1) + 1)[1]
        y = (a/b)
        # println(y)
        prob_equals(y[1], res) & !y[2]
    end
    code
end

# BDD analysis
code = code_div(1, 1, 2)
bdd = compile(code)
# println(infer(code, :bdd))
@assert infer(code, :bdd) ≈ 0.25

code = code_div(2, 1, 2)
bdd = compile(code)
@assert infer(code, :bdd) ≈ 0.25

code = code_div(2, 1, 4)
bdd = compile(code)
@assert infer(code, :bdd) ≈ 0.125

code = code_div(1, 2, 0)
bdd = compile(code)
@assert infer(code, :bdd) ≈ 0.625

code = code_div(1, 2, 1)
bdd = compile(code)
@assert infer(code, :bdd) ≈ 0.25

code = code_div(1, 2, 2)
bdd = compile(code)
@assert infer(code, :bdd) ≈ 0.125
# #         bdd = compile(code)
# # num_flips(bdd)
# # num_nodes(bdd)
# # @assert infer(code, :bdd) == 0.0625

# IR analysis
# to_dice_ir(code)
# has_dice_binary() && rundice(code)
# has_dice_binary() && infer(code, :ocaml)