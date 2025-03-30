using Revise
using Alea
using Alea: num_flips, num_nodes, to_dice_ir

@macroexpand @alea_ite

code = @alea_ite begin
    function uniform(b::Int, w::Int) # b is the bits for uniform, w is the bitwidth
        x = Vector(undef, b)
        for i = b:-1:1
            x[i] = flip(0.5)
        end
        return add_bits(DistInt(x), w - b)
    end
    uniform(2, 2)
end

# BDD analysis
bdd = compile(code)
num_flips(bdd)
num_nodes(bdd)
infer(code, :bdd)

# IR analysis
# to_dice_ir(code)
# has_dice_binary() && rundice(code)
# has_dice_binary() && infer(code, :ocaml)