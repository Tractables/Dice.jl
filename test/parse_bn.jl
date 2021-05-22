using HTTP
using Dice
using Lerche

# bn = "cancer";
# bn = "survey";
bn = "alarm";
# bn = "pigs";
# bn = "munin";

r = HTTP.request("GET", "https://raw.githubusercontent.com/SHoltzen/dice/master/benchmarks/bayesian-networks/$bn.bif.dice");
bn_code = String(r.body);

@time dice_expr = Dice.parse(Dice.DiceProgram, bn_code);

# manual
# dice_parser =  Lark(Dice.dice_grammar, parser="lalr", lexer="contextual")
# bn_ast = Lerche.parse(dice_parser, bn_code);
# Lerche.transform(Dice.DiceTransformer(), bn_ast);

@time c = Dice.compile(dice_expr);
Dice.num_nodes(c)
Dice.num_flips(c)

