using Pkg; Pkg.activate("Dice/test");
using HTTP
using Dice

bns = ["cancer", "andes", "asia", "child", "earthquake", "hailfinder", "hepar2", "insurance", "mildew", "survey", "pathfinder", "sachs", "survey", "win95pts", "alarm", "pigs", "water", "munin", "munin1", "munin2", "munin3", "munin4", "link", "diabetes", "barley"]

bn = bns[15] # alarm
bn = bns[23] # link
bn = "insurance"


r = HTTP.request("GET", "https://raw.githubusercontent.com/ellieyhcheng/dice/master/benchmarks/bayesian-networks//$bn.dice"); nothing;
bn_code = String(r.body); nothing;

@time dice_expr = Dice.parse(Dice.DiceProgram, bn_code); nothing;

# manual
# using Lerche
# dice_parser =  Lark(Dice.dice_grammar, parser="lalr", lexer="contextual")
# bn_ast = Lerche.parse(dice_parser, bn_code);
# Lerche.transform(Dice.DiceTransformer(), bn_ast);

@time c = Dice.compile(dice_expr); nothing;

Dice.num_nodes(c)
Dice.num_flips(c)
Dice.num_vars(c.mgr)

custom_strategy = (Dice.default_strategy()..., categorical = :sangbeamekautz,)
custom_strategy = (Dice.default_strategy()..., branch_elim = :none,)
custom_strategy = (Dice.default_strategy()..., branch_elim = :guard_bdd,)
custom_strategy = (Dice.default_strategy()..., branch_elim = :path_bdd,)
custom_strategy = (Dice.default_strategy()..., branch_elim = :nested_guard_bdd,)


custom_strategy = (Dice.default_strategy()..., debug=1, var_order = :program_order,)
custom_strategy = (Dice.default_strategy()..., debug=1, var_order = :dfs,)
custom_strategy = (Dice.default_strategy()..., debug=1, var_order = :metis_cut,)
custom_strategy = (Dice.default_strategy()..., debug=1, var_order = :metis_perm,)
custom_strategy = (Dice.default_strategy()..., debug=1, var_order = :metis_perm_rev,)
custom_strategy = (Dice.default_strategy()..., debug=1, var_order = :min_gap,)
custom_strategy = (Dice.default_strategy()..., debug=0, var_order = :min_gap,)
custom_strategy = (Dice.default_strategy()..., debug=1, var_order = :test,)
(c = @time (Dice.compile(dice_expr, Dice.CuddMgr(custom_strategy)))); nothing
Dice.num_nodes(c)



# ground truth size
Dice.run_dice(bn_code; skiptable=true, determinism=true, showsize=true)
   

@time s, _ = Dice.support(dice_expr)
Dice.num_nodes(s)

# try making a single BDD
roots = Dice.bools(c)
onebdd = Dice.true_constant(roots[1].mgr)
for r in roots
    equiv = Dice.prob_equals(Dice.flip(r.mgr), r)
    onebdd = Dice.:&(onebdd, equiv)
    println("Nodes: $(Dice.num_nodes(onebdd)))")
end

custom_strategy = (Dice.default_strategy()..., include_indicators = true)
@time c = Dice.compile(dice_expr, Dice.CuddMgr(custom_strategy)); nothing;

g = Dice.id_dep_graph(dice_expr); nothing;
Dice.plot(g);
Dice.plot(g; order = :program_order);
Dice.plot(g; order = :test);
Dice.plot(g; order = :dfs);
Dice.plot(g; order = :metis_cut);
Dice.plot(g; order = :min_gap);
Dice.plot(g; order = :test);

Dice.topological_sort_by_dfs(g)