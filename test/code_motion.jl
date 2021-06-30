using Pkg; Pkg.activate("Dice/test");
using HTTP
using Dice

bns = ["cancer", "andes", "asia", "child", "earthquake", "hailfinder", "hepar2", "insurance", "mildew", "survey", "pathfinder", "sachs", "survey", "win95pts", "alarm", "pigs", "water", "munin", "munin1", "munin2", "munin3", "munin4", "link", "diabetes", "barley"]

bn = bns[3]

for bn in bns

    r = HTTP.request("GET", "https://raw.githubusercontent.com/ellieyhcheng/dice/master/benchmarks/bayesian-networks//$bn.dice"); nothing;
    bn_code = String(r.body); nothing;

    dice_expr = Dice.parse(Dice.DiceProgram, bn_code); nothing;

    opt_expr = Dice.code_motion(dice_expr, :min_gap); nothing

    open("dice_opt/$bn.opt.dice", "w") do io
        print(io, opt_expr)
    end

    println("Saved optimized $bn")

end

g = Dice.id_dep_graph(dice_expr); nothing;
g = Dice.id_dep_graph(opt_expr); nothing;
Dice.plot(g; order = :program_order);
