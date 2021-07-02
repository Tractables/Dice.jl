using Pkg; Pkg.activate("Dice/test");
using HTTP
using Dice

# roughly ranked by file size
bns = ["cancer", "andes", "asia", "child", "earthquake", "hailfinder", "hepar2", "insurance", "mildew", "survey", "pathfinder", "sachs", "survey", "win95pts", "alarm", "pigs", "water", "munin", "munin1", "munin2", "munin3", "munin4", "link", "diabetes", "barley"]

bn = "alarm"
bn = "hailfinder"
bn = "pigs"
bn = "link"
bn = "munin"

order = :min_gap
# munin: 14823970
# link:   1690520

order = :min_gap_flips
# munin: 13963072
# link:   1690520

# for bn in bns

    r = HTTP.request("GET", "https://raw.githubusercontent.com/ellieyhcheng/dice/master/benchmarks/bayesian-networks//$bn.dice"); nothing;
    bn_code = String(r.body); nothing;

    dice_expr = Dice.parse(Dice.DiceProgram, bn_code); nothing;

    opt_expr = Dice.code_motion(dice_expr, order); nothing

    open("dice_opt/$bn.opt.dice", "w") do io
        print(io, opt_expr)
    end
    open("dice_opt/$bn.dice", "w") do io
        print(io, dice_expr)
    end

    println("Saved optimized $bn")

# end

# our compilation without code motion
custom_strategy = (Dice.default_strategy()..., debug=0,)
(c = @time (Dice.compile(dice_expr, Dice.CuddMgr(custom_strategy)))); nothing
Dice.num_nodes(c)
Dice.num_flips(c)
Dice.num_vars(c.mgr)

# ground truth compilation without code motion
@time Dice.num_nodes_ocml(dice_expr)

# our compilation with code motion built in
custom_strategy = (Dice.default_strategy()..., debug=0, var_order = order,)
(c = @time (Dice.compile(dice_expr, Dice.CuddMgr(custom_strategy)))); nothing
Dice.num_nodes(c)
Dice.num_flips(c)
Dice.num_vars(c.mgr)

# our compilation after code motion
custom_strategy = (Dice.default_strategy()..., debug=0,)
(c = @time (Dice.compile(opt_expr, Dice.CuddMgr(custom_strategy)))); nothing
Dice.num_nodes(c)
Dice.num_flips(c)

# ground truth after code motion
@time Dice.num_nodes_ocml(opt_expr)

using Test
@test Flip(0.7) != Flip(0.7)
@test Categorical([0.1,0.9]) != Categorical([0.1,0.9])

# dependency graph debugging
g = Dice.id_dep_graph(dice_expr); nothing;
g = Dice.id_dep_graph(opt_expr); nothing;
Dice.plot(g);
Dice.plot(g; order = :program_order);
Dice.plot(g; order);
op