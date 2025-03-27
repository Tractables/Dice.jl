using Alea
using Alea: num_flips, num_nodes

probs = [1/i for i=2:20]
res = mapreduce(p -> !flip(p), &, probs)  # all tails
# BDD analysis
num_flips(res)
num_nodes(res)
# infer_bool(res)

# IR analysis
# println(to_dice_ir(code))
# has_dice_binary() && rundice(code)
# has_dice_binary() && infer(code, :ocaml)
