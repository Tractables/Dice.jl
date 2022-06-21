using Dice
using Dice: num_flips, num_nodes

function my_uniform(b::Int, w::Int) # b is the bits for uniform, w is the bitwidth
    x = Vector(undef, b)
    for i = b:-1:1
        x[i] = flip(0.5)
    end
    return add_bits(DistInt(x), w - b)
end

function cg_arith(f, b1::Int, b2::Int, res::Int)
    a = (my_uniform(b1, b1))
    b = (my_uniform(b2, b2))
    y = f(a, b)
    prob_equals(y[1], res) & !y[2]
end

# BDD analysis
cg = cg_arith(+, 2, 2, 0)
@assert infer_bool(cg) ≈ 0.0625

cg = cg_arith(+, 2, 3, 0)
@assert infer_bool(cg) ≈ 0.03125

cg = cg_arith(+, 3, 2, 0)
@assert infer_bool(cg) ≈ 0.03125

cg = cg_arith(-, 2, 2, 0)
@assert infer_bool(cg) ≈ 0.25

cg = cg_arith(-, 1, 2, 0)
@assert infer_bool(cg) ≈ 0.25

cg = cg_arith(-, 3, 2, 0)
@assert infer_bool(cg) ≈ 0.125

cg = cg_arith(*, 2, 2, 0)
@assert infer_bool(cg) ≈ 0.4375

cg = cg_arith(*, 1, 2, 0)
@assert infer_bool(cg) ≈ 0.625

cg = cg_arith(*, 3, 2, 0)
@assert infer_bool(cg) ≈ 0.34375
