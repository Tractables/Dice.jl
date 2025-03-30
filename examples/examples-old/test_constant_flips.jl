using Alea
using Alea: num_flips, num_nodes

seven = Alea.ifelse(flip(0), DistInt(3), DistInt(7))
hundred = Alea.ifelse(flip(1), DistInt(100), DistInt(200))
cg = (seven + hundred)[1]

res = infer(cg)
@assert length(res) == 1
@assert res[107] == 1
@assert num_flips(cg) == 0
