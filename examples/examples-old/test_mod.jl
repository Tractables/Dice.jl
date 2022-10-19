using Dice
using Dice: num_flips, num_nodes

function my_uniform(b::Int, w::Int) # b is the bits for uniform, w is the bitwidth
    x = Vector(undef, b)
    for i = b:-1:1
        x[i] = flip(0.5)
    end
    return add_bits(DistInt(x), w - b)
end

function cg_div(b1::Int, b2::Int, res::Int)
    a = (my_uniform(b1, b1+1) + 1)[1]
    b = (my_uniform(b2, b2+1))
    y = (a%b)
    # println(y)
    prob_equals(y[1], res) & !y[2]
end

# BDD analysis
cg = cg_div(1, 1, 0)
println(infer_bool(cg))
@assert infer_bool(cg) ≈ 0.5

cg = cg_div(2, 1, 1)
@assert infer_bool(cg) ≈ 0

cg = cg_div(2, 1, 0)
@assert infer_bool(cg) ≈ 0.5

cg = cg_div(1, 2, 0)
@assert infer_bool(cg) ≈ 0.375

cg = cg_div(1, 2, 2)
@assert infer_bool(cg) ≈ 0.125

# #         bdd = compile(code)
# # num_flips(bdd)
# # num_nodes(bdd)
# # @assert infer(code, :bdd) == 0.0625

# IR analysis
# to_dice_ir(code)
# has_dice_binary() && rundice(code)
# has_dice_binary() && infer(code, :ocaml)