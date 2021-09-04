using Pkg; Pkg.activate("Dice/test");
using HTTP
using Dice

var_order = :program_order
var_order = :min_gap
var_order = :dfs
var_order = :dfs_rev
var_order = :metis_perm
var_order = :metis_perm_rev
var_order = :metis_cut
var_order = :min_gap_flips
var_order = :min_gap_flips_interleave
var_order = :min_gap_flips_interleave_all

categorical = :bitwiseholtzen
categorical = :sangbeamekautz

debug = 0

for bn in ["alarm"] 
# for bn in ["alarm", "insurance", "water", "hailfinder", "munin", "link", "pigs"]

    r = HTTP.request("GET", "https://raw.githubusercontent.com/ellieyhcheng/dice/master/benchmarks/bayesian-networks//$bn.dice"); nothing;
    bn_code = String(r.body); nothing;

    dice_expr = Dice.parse(Dice.DiceProgram, bn_code); nothing;

    # compile indicators
    custom_strategy = (Dice.default_strategy()..., debug=debug, var_order=var_order, categorical=categorical, )
    @time (c = Dice.comp_ind(dice_expr, Dice.CuddMgr(custom_strategy)))
    s = Dice.num_nodes(c)
    println("# $bn:  $s")

end

### program_order, bitwiseholtzen
# alarm:  2860240
# insurance:  476784
# water:  456563
# hailfinder:  134021

### min_gap, bitwiseholtzen
# alarm:  508363
# insurance:  3979323

### dfs, bitwiseholtzen
# alarm:  5887
# insurance:  2175491
# water:  144373

### dfs_rev, bitwiseholtzen
# /

### metis_perm, bitwiseholtzen
# /

### metis_perm_rev, bitwiseholtzen
# /

### metis_cut, bitwiseholtzen
# alarm:  92651


### min_gap_flips, bitwiseholtzen
# alarm:  508355
# insurance:  1332222
# water:  181821
# hailfinder:  128321

### min_gap_flips_interleave, bitwiseholtzen
# alarm:  5040
# insurance:  318800
# water:  398433
# hailfinder:  128321


### min_gap_flips_interleave_all, bitwiseholtzen
# alarm:  410989
# insurance:  704520
# water:  1021879