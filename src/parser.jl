using Lerche: Lerche, Lark, Transformer, @rule, @inline_rule

const dice_grammar = raw"""
    start: expr

    ?expr: bool
         | identifier
         | flip
         | discrete
         | integer
         | "(" expr ")"
         | expr "==" expr -> equals_op
         | "(" expr "," expr ")" -> tuple
         | "if" expr "then" expr "else" expr -> ite
         | "let" identifier "=" expr "in" expr -> let_expr

    bool: "true"             -> bool_t
        | "false"            -> bool_f

    flip: "flip" prob
    discrete: "discrete" "(" prob ("," prob)* ")"
    integer: "int" "(" INT "," INT ")"
    prob: FLOAT
    identifier: CNAME

    %import common.FLOAT
    %import common.INT
    %import common.WS
    %import common.CNAME
       
    %ignore WS
    """
    
struct DiceTransformer <: Transformer end

@rule bool_t(t::DiceTransformer, x) = true
@rule bool_f(t::DiceTransformer, x) = false
@rule integer(t::DiceTransformer, x) = Base.parse(Int,x[2])
@inline_rule prob(t::DiceTransformer, x) = Base.parse(Float64,x)
@inline_rule flip(t::DiceTransformer, x) = Flip(x)
@rule discrete(t::DiceTransformer, x) = Categorical(x)
@inline_rule identifier(t::DiceTransformer, x) = Identifier(x)
@rule equals_op(t::DiceTransformer, x) = EqualsOp(x[1],x[2])
@rule tuple(t::DiceTransformer, x) = DiceTuple(x[1], x[2])
@rule ite(t::DiceTransformer, x) = Ite(x[1],x[2],x[3])
@rule let_expr(t::DiceTransformer, x) = LetExpr(x[1],x[2],x[3])
@inline_rule start(t::DiceTransformer, x) = DiceProgram(x)

const dice_parser = 
    Lark(dice_grammar, parser="lalr", lexer="contextual"; 
         transformer = DiceTransformer())

parse(::Type{DiceProgram}, str)::DiceProgram = 
    Lerche.parse(dice_parser, str)

read(io::IO, ::Type{DiceProgram}) =
    parse(DiceProgram, read(io, String))

