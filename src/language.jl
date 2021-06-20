export DiceProgram, Flip, Categorical, DiceTuple, Identifier, EqualsOp, Ite, LetExpr

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

num_bits(i::Int) = ceil(Int,log2(i+1))
num_bits(x::Ite) = 
    max(num_bits(x.then_expr),num_bits(x.else_expr))
    
function num_bits(x::Categorical)
    max_val = findlast(p -> !iszero(p), x.probs) - 1
    num_bits(max_val)
end

# TODO add other cases for num_bits?