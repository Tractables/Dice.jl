using Dice
using Dice: num_flips, num_nodes

seven = Dice.ifelse(flip(0), DistInt(3), DistInt(7))
hundred = Dice.ifelse(flip(1), DistInt(100), DistInt(200))
cg = (seven + hundred)[1]

res = infer(cg)
@assert length(res) == 1
@assert res[107] == 1
@assert num_flips(cg) == 0
