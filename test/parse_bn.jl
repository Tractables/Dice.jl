using HTTP
using Dice
using Lerche

# bn = "munin";
bn = "cancer";
r = HTTP.request("GET", "https://raw.githubusercontent.com/SHoltzen/dice/master/benchmarks/bayesian-networks/$bn.bif.dice");
bn_code = String(r.body);


dice_parser = 
    Lark(Dice.dice_grammar, parser="lalr", lexer="contextual")
bn_ast = Lerche.parse(Dice.dice_parser, bn_code);

Lerche.transform(Dice.DiceTransformer(), bn_ast);
