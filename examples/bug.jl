using Dice
using Dice: num_flips, num_nodes, to_dice_ir

code = @dice begin
    x = flip(0.5)
    y = if x x else false
    if y y else false
end

# BDD analysis
bdd = compile(code)
num_flips(bdd), num_nodes(bdd)
infer(code, :bdd)

# IR analysis
println(to_dice_ir(code))
has_dice_binary() && rundice(code)
has_dice_binary() && infer(code, :ocaml)
