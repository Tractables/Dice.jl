using Alea
using Alea: num_flips, num_nodes, to_dice_ir

code = @dice_ite begin
    n = 10
    x = Vector(undef, n)
    x[1] = flip(0.5)
    for i=2:n
        x[i] = if x[i-1]
            flip(0.9)
        else
            flip(0.4)
        end
    end
    x[end]
end

# BDD analysis
bdd = compile(code)
num_flips(bdd)
num_nodes(bdd)
infer(code, :bdd)

# IR analysis
to_dice_ir(code)
has_dice_binary() && rundice(code)
has_dice_binary() && infer(code, :ocaml)
