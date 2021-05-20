using HTTP

bn = "munin";
r = HTTP.request("GET", "https://raw.githubusercontent.com/SHoltzen/dice/master/benchmarks/bayesian-networks/$bn.bif.dice");
bn_code = String(r.body);

using Lerche

dice_grammar = raw"""
    start: expr

    expr: IDENT -> identifier
        | discrete
        | integer
        | "(" expr ")"
        | expr BINOP expr -> binexpr
        | "(" expr "," expr ")" -> tuple
        | "if" expr "then" expr "else" expr -> ite
        | "let" IDENT "=" expr "in" expr -> letst

    discrete: "discrete" "(" PROB ("," PROB)* ")"
    integer: "int" "(" INT "," INT ")"

    BINOP: "=="

    %import common.FLOAT -> PROB
    %import common.INT
    %import common.WS
    %import common.CNAME -> IDENT
       
    %ignore WS
    """;
    
dice_parser = Lark(dice_grammar);

bn_ast = Lerche.parse(dice_parser, bn_code);