using Pkg; Pkg.activate("Dice/test");
using HTTP
using Dice

# roughly ranked by file size
bns = ["cancer", "andes", "asia", "child", "earthquake", "hailfinder", "hepar2", "insurance", "mildew", "survey", "pathfinder", "sachs", "survey", "win95pts", "alarm", "pigs", "water", "munin", "munin1", "munin2", "munin3", "munin4", "link", "diabetes", "barley"]

bn = "alarm"
bn = "insurance"
bn = "hailfinder"
bn = "pigs"
bn = "munin"
bn = "link"

order = :program_order
# alarm:  293903
# insurance:  112628
# water:  44705
# hailfinder:  147333
# pigs:  180124
# link:     15117830
# munin:     4998135

order = :metis_cut

order = :min_gap
# alarm:  10874
# insurance:  243286
# water:  45181
# hailfinder:  137709
# pigs:  67577
# link:  1690520
# munin:    14522982

order = :min_gap_flips
# alarm:  10874
# insurance:  318764
# water:  18407
# hailfinder:  137709
# pigs:  67577
# link:      9268685
# munin:    14450428

order = :min_gap_flips_interleave
# alarm:  10874
# insurance:  318764
# water:  18673
# hailfinder:  137709
# pigs:  61207
# link:      3389991
# munin: /

order = :test

categorical = :bitwiseholtzen
# categorical = :sangbeamekautz

# for bn in bns
for bn in ["alarm", "insurance", "water", "hailfinder", "pigs", "link", "munin"]
    # for bn in ["alarm", "insurance", "water",  "pigs", "link", "munin"]

    r = HTTP.request("GET", "https://raw.githubusercontent.com/ellieyhcheng/dice/master/benchmarks/bayesian-networks//$bn.dice"); nothing;
    bn_code = String(r.body); nothing;

    dice_expr = Dice.parse(Dice.DiceProgram, bn_code); nothing;
    "hailfinder", 
    # opt_expr = Dice.code_motion(dice_expr, order); nothing

    # open("dice_opt/$bn.opt.dice", "w") do io
    #     print(io, opt_expr)
    # end
    # open("dice_opt/$bn.dice", "w") do io
    #     print(io, dice_expr)
    # end

    # println("Saved optimized $bn")

    # our compilation with code motion built in
    custom_strategy = (Dice.default_strategy()..., debug=0, var_order = order, categorical, )
    c = Dice.compile(dice_expr, Dice.CuddMgr(custom_strategy))
    s = Dice.num_nodes(c)
    println("# $bn:  $s")

end

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


# NO CODE MOTION

# our compilation without code motion
custom_strategy = (Dice.default_strategy()..., debug=0,)
(c = @time (Dice.compile(dice_expr, Dice.CuddMgr(custom_strategy)))); nothing
Dice.num_nodes(c)
Dice.num_flips(c)
Dice.num_vars(c.mgr)

# ground truth compilation without code motion
@time Dice.num_nodes_ocml(dice_expr)


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