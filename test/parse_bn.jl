using Pkg; Pkg.activate("Dice/test");
using HTTP
using Dice

bn = "cancer";
bn = "survey";
bn = "alarm";
bn = "pigs";
bn = "water";
bn = "munin";
bn = "munin1";
bn = "munin2";
bn = "munin3";
bn = "munin4";
bn = "diabetes";

r = HTTP.request("GET", "https://raw.githubusercontent.com/ellieyhcheng/dice/master/benchmarks/bayesian-networks//$bn.dice"); nothing;
bn_code = String(r.body); nothing;

@time dice_expr = Dice.parse(Dice.DiceProgram, bn_code); nothing;

# manual
# using Lerche
# dice_parser =  Lark(Dice.dice_grammar, parser="lalr", lexer="contextual")
# bn_ast = Lerche.parse(dice_parser, bn_code);
# Lerche.transform(Dice.DiceTransformer(), bn_ast);

@time c = Dice.compile(dice_expr); nothing;

custom_strategy = (Dice.default_strategy()..., categorical = :sangbeamekautz,)
custom_strategy = (Dice.default_strategy()..., branch_elim = :none,)
custom_strategy = (Dice.default_strategy()..., branch_elim = :guard_bdd,)
custom_strategy = (Dice.default_strategy()..., branch_elim = :path_bdd,)
custom_strategy = (Dice.default_strategy()..., branch_elim = :nested_guard_bdd,)
custom_strategy = (Dice.default_strategy()..., var_order = :dfs,)
custom_strategy = (Dice.default_strategy()..., var_order = :metis_cut,)
@time c = Dice.compile(dice_expr, Dice.CuddMgr(custom_strategy)); nothing;

Dice.num_nodes(c)
Dice.num_flips(c)
Dice.num_vars(c.mgr)

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
Dice.plot(g; order = :dfs);
Dice.plot(g; order = :metis_cut);

Dice.topological_sort_by_dfs(g)