export DiceProgram

abstract type CustomDiceExpr end

const DiceExpr = Union{CustomDiceExpr, Int, Bool}

struct DiceProgram
    expr::DiceExpr
end
struct Flip <: CustomDiceExpr
    prob::Float64    
end

struct Categorical <: CustomDiceExpr
    probs::Vector{Float64}    
end

struct DiceTuple <: CustomDiceExpr
    # avoid too many nested type parameters by not using Tuple here
    first::DiceExpr
    second::DiceExpr
end

struct Identifier <: CustomDiceExpr
    symbol::String    
end

struct EqualsOp <: CustomDiceExpr
    e1::DiceExpr
    e2::DiceExpr
end

struct Ite <: CustomDiceExpr
    cond_expr::DiceExpr
    then_expr::DiceExpr
    else_expr::DiceExpr
end

struct LetExpr <: CustomDiceExpr
    identifier::Identifier
    e1::DiceExpr
    e2::DiceExpr
end
