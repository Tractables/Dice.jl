using Dice
using Dice: num_flips, num_nodes, to_dice_ir

chain = @dice begin
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

bdd = compile(chain)
println("Number of flips used: $(num_flips(bdd))")
println("Number of BDD nodes: $(num_nodes(bdd))")

ir = to_dice_ir(chain)
print(ir.bit)
has_dice_binary() && rundice(ir)
has_dice_binary() && rundice(chain)
