using Dice
using Dice: num_flips, num_nodes

code = @dice begin
    seven = if flip(0) DistInt(3) else DistInt(7) end
    hundred = if flip(1) DistInt(100) else DistInt(200) end
    (seven + hundred)[1]
end

bdd = compile(code)
res = infer(bdd)
@assert length(res) == 1
@assert res[107] == 1
@assert num_flips(bdd) == 0
