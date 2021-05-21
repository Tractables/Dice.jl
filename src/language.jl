struct DiceProgram
    expr
end

struct Categorical
    probs::Vector{Float64}    
end

struct Identifier
    symbol::String    
end

struct EqualsOp
    e1
    e2    
end

struct Ite
    if_expr
    then_expr
    else_expr
end

struct LetExpr
    identifier::Identifier
    e1
    e2 
end
