using Dice
using Dice: num_flips, num_nodes

function code_arith(f, b1::Int, b2::Int, res::Int)
    code = @dice begin
        function uniform(b::Int, w::Int) # b is the bits for uniform, w is the bitwidth
            x = Vector(undef, b)
            for i = b:-1:1
                x[i] = flip(0.5)
            end
            return add_bits(DistInt(x), w - b)
        end
        a = (uniform(b1, b1))
        b = (uniform(b2, b2))
        y = f(a, b)
        prob_equals(y[1], res) & !y[2]
    end
    code
end

# BDD analysis
code = code_arith(+, 2, 2, 0)
@assert infer_bool(code) ≈ 0.0625

code = code_arith(+, 2, 3, 0)
@assert infer_bool(code) ≈ 0.03125

code = code_arith(+, 3, 2, 0)
@assert infer_bool(code) ≈ 0.03125

code = code_arith(-, 2, 2, 0)
@assert infer_bool(code) ≈ 0.25

code = code_arith(-, 1, 2, 0)
@assert infer_bool(code) ≈ 0.25

code = code_arith(-, 3, 2, 0)
@assert infer_bool(code) ≈ 0.125

code = code_arith(*, 2, 2, 0)
@assert infer_bool(code) ≈ 0.4375

code = code_arith(*, 1, 2, 0)
@assert infer_bool(code) ≈ 0.625

code = code_arith(*, 3, 2, 0)
@assert infer_bool(code) ≈ 0.34375
