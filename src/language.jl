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

show_dice(io, e, ident) =
    show(io, e, ident)

# intercept int expressions
function show_dice(io, e::Int, ident)
    b = num_bits(e)
    print(io, "int($b,$e)")    
end

Base.show(io::IO, x::DiceProgram) =
    show_dice(io, x.expr, 0) 

function Base.show(io::IO, e::LetExpr, ident = 0)
    println(io, "let $(e.identifier) = ")
    print_identation(io, ident + 1)    
    show_dice(io, e.e1, ident + 1)
    println(io, " in")
    print_identation(io, ident)    
    show_dice(io, e.e2, ident) 
end

function Base.show(io::IO, e::Categorical, ident = 0)
    print(io, "discrete(")
    join(io, e.probs, ", ")
    print(io, ")") 
end

function Base.show(io::IO, e::Flip, ident = 0)
    print(io, "flip $(e.prob)")
end

function Base.show(io::IO, e::Ite, ident = 0)
    print(io, "if ")
    show_dice(io, e.cond_expr, ident)
    println(io, " then")
    print_identation(io, ident+1)    
    show_dice(io, e.then_expr, ident + 1)
    println(io)
    print_identation(io, ident)    
    println(io, "else")
    print_identation(io, ident+1)    
    show_dice(io, e.else_expr, ident + 1) 
end

function Base.show(io::IO, e::DiceTuple, ident = 0)
    print(io, "(") 
    show_dice(io, e.first, ident)
    print(io, ", ") 
    show_dice(io, e.second, ident)
    print(io, ")") 
end

function Base.show(io::IO, e::EqualsOp, ident = 0)
    show_dice(io, e.e1, ident)
    print(io, " == ") 
    show_dice(io, e.e2, ident)
end

function Base.show(io::IO, e::Identifier, ident = 0)
    print(io, e.symbol) 
end

print_identation(io, ident) =
    print("  "^ident)

