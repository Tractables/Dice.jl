using Pkg; Pkg.activate("Dice/test");
using HTTP
using Dice

# bn = "cancer";
# bn = "survey";
# bn = "alarm";
# bn = "pigs";
# bn = "water";
bn = "munin";

r = HTTP.request("GET", "https://raw.githubusercontent.com/SHoltzen/dice/master/benchmarks/bayesian-networks/$bn.bif.dice");
bn_code = String(r.body); nothing;

@time dice_expr = Dice.parse(Dice.DiceProgram, bn_code); nothing;
@time dice_expr = Dice.parse(Dice.DiceProgram, bn_code); nothing;

# manual
# using Lerche
# dice_parser =  Lark(Dice.dice_grammar, parser="lalr", lexer="contextual")
# bn_ast = Lerche.parse(dice_parser, bn_code);
# Lerche.transform(Dice.DiceTransformer(), bn_ast);

@time c = Dice.compile(dice_expr); nothing;
@time c = Dice.compile(dice_expr); nothing;
@time c = Dice.compile(dice_expr, (categorical = :sangbeamekautz,)); nothing;

Dice.num_nodes(c)
Dice.num_flips(c)

# ground truth size
Dice.run_dice(bn_code; skiptable=true, determinism=true, showsize=true)
   
