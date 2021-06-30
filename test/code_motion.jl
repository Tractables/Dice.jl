using Pkg; Pkg.activate("Dice/test");
using HTTP
using Dice

bns = ["cancer", "survey", "alarm", "pigs", "water", "munin", "munin1", "munin2", "munin3", "munin4", "link", "diabetes", "barley"]

bn = bns[1]

r = HTTP.request("GET", "https://raw.githubusercontent.com/ellieyhcheng/dice/master/benchmarks/bayesian-networks//$bn.dice"); nothing;
bn_code = String(r.body); nothing;

dice_expr = Dice.parse(Dice.DiceProgram, bn_code); nothing;

opt_expr = Dice.code_motion(dice,expr, :min_gap)