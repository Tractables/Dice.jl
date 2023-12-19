export ADNode, ADMatrix, Variable, Var, ad_map, sigmoid, deriv_sigmoid, inverse_sigmoid

import DirectedAcyclicGraphs: NodeType, DAG, children

abstract type ADNode <: DAG end

# We always differentiate with respect to Variables
abstract type Variable <: ADNode end

NodeType(::Type{<:Variable}) = Leaf()
compute_leaf(x::Variable) = error("The value of $(x) should've been provided in `vals`!")
backward(::Variable, _, _) = nothing

ADNodeCompatible = Union{Real, AbstractMatrix{<:Real}}

function add_deriv(derivs, n::ADNode, amount::ADNodeCompatible)
    if haskey(derivs, n)
        derivs[n] += amount
    else
        derivs[n] = amount
    end
end


struct Var <: Variable
    id::Any
end
function Base.show(io::IO, x::Var)
    print(io, "Var(")
    show(io, x.id)
    print(io, ")")
end

struct Constant <: ADNode
    value::ADNodeCompatible
end
NodeType(::Type{Constant}) = Leaf()
compute_leaf(x::Constant) = x.value
backward(::Constant, _, _) = nothing
function Base.show(io::IO, x::Constant)
    print(io, "Constant(")
    show(io, x.value)
    print(io, ")")
end

struct Add <: ADNode
    x::ADNode
    y::ADNode
end
NodeType(::Type{Add}) = Inner()
children(x::Add) = [x.x, x.y]
compute_inner(x::Add, call) = call(x.x) + call(x.y)
function backward(n::Add, vals, derivs)
    add_deriv(derivs, n.x, derivs[n])
    add_deriv(derivs, n.y, derivs[n])
end
Base.:(+)(x::ADNode, y::ADNode) = Add(x, y)
Base.:(+)(x::ADNode, y::ADNodeCompatible) = Add(x, Constant(y))
Base.:(+)(x::ADNodeCompatible, y::ADNode) = Add(Constant(x), y)

struct Mul <: ADNode
    x::ADNode
    y::ADNode
end
NodeType(::Type{Mul}) = Inner()
children(x::Mul) = [x.x, x.y]
compute_inner(x::Mul, call) = call(x.x) * call(x.y)
function backward(n::Mul, vals, derivs)
    if derivs[n] isa Real
        add_deriv(derivs, n.x, derivs[n] * vals[n.y])
        add_deriv(derivs, n.y, derivs[n] * vals[n.x])
    elseif derivs[n] isa AbstractMatrix{<:Real}
        add_deriv(derivs, n.x, derivs[n] * transpose(vals[n.y]))
        add_deriv(derivs, n.y, transpose(vals[n.x]) * derivs[n])
    else
        error("bad derivs type")
    end
end
Base.:(*)(x::ADNode, y::ADNode) = Mul(x, y)
Base.:(*)(x::ADNode, y::ADNodeCompatible) = Mul(x, Constant(y))
Base.:(*)(x::ADNodeCompatible, y::ADNode) = Mul(Constant(x), y)

# struct Div <: ADNode
#     x::ADNode
#     y::ADNode
# end
# NodeType(::Type{Div}) = Inner()
# children(x::Div) = [x.x, x.y]
# compute_inner(x::Div, call) = call(x.x) / call(x.y)
# function backward(n::Div, vals, derivs)
#     derivs[n.x] += derivs[n] / vals[n.y]
#     derivs[n.y] -= derivs[n] * vals[n.x] / vals[n.y] ^ 2
# end
# Base.:(/)(x::ADNode, y::ADNode) = Div(x, y)
# Base.:(/)(x::ADNode, y::Real) = Div(x, Constant(y))
# Base.:(/)(x::Real, y::ADNode) = Div(Constant(x), y)

struct Pow <: ADNode
    x::ADNode
    y::ADNode
end
NodeType(::Type{Pow}) = Inner()
children(x::Pow) = [x.x, x.y]
compute_inner(x::Pow, call) = call(x.x) ^ call(x.y)
function backward(n::Pow, vals, derivs)
    @assert derivs[n] isa Real
    add_deriv(derivs, n.x, derivs[n] * vals[n.y] * vals[n.x] ^ (vals[n.y] - 1))
    if !(n.y isa Constant)
        add_deriv(derivs, n.y, derivs[n] * log(vals[n.x]) * vals[n.x] ^ vals[n.y])
    end
end
Base.:(^)(x::ADNode, y::ADNode) = Pow(x, y)
Base.:(^)(x::ADNode, y::ADNodeCompatible) = Pow(x, Constant(y))
Base.:(^)(x::ADNodeCompatible, y::ADNode) = Pow(Constant(x), y)

struct Sin <: ADNode
    x::ADNode
end
NodeType(::Type{Sin}) = Inner()
children(x::Sin) = [x.x]
compute_inner(x::Sin, call) = sin(call(x.x))
function backward(n::Sin, vals, derivs)
    @assert derivs[n] isa Real
    add_deriv(derivs, n.x, derivs[n] * cos(vals[n.x]))
end
Base.sin(x::ADNode) = Sin(x)

struct Cos <: ADNode
    x::ADNode
end
NodeType(::Type{Cos}) = Inner()
children(x::Cos) = [x.x]
compute_inner(x::Cos, call) = cos(call(x.x))
function backward(n::Cos, vals, derivs)
    @assert derivs[n] isa Real
    add_deriv(derivs, n.x, derivs[n] * -sin(vals[n.x]))
end
Base.cos(x::ADNode) = Cos(x)

# struct Exp <: ADNode
#     x::ADNode
# end
# NodeType(::Type{Exp}) = Inner()
# children(x::Exp) = [x.x]
# compute_inner(x::Exp, call) = exp(call(x.x))
# function backward(n::Exp, vals, derivs)
#     derivs[n.x] += derivs[n] * exp(vals[n.x])
# end
# Base.exp(x::ADNode) = Exp(x)

struct Log <: ADNode
    x::ADNode
end
NodeType(::Type{Log}) = Inner()
children(x::Log) = [x.x]
compute_inner(x::Log, call) = log(call(x.x))
function backward(n::Log, vals, derivs)
    @assert derivs[n] isa Real
    add_deriv(derivs, n.x, derivs[n] / vals[n.x])
end
Base.log(x::ADNode) = Log(x)

struct ADMatrix <: ADNode
    x::AbstractMatrix{ADNode}
    function ADMatrix(x::AbstractMatrix{<:Union{<:Real, ADNode}})
        x isa AbstractMatrix{ADNode} && return new(x)
        cast(x::ADNode) = x
        cast(x::Real) = Constant(x)
        new(map(cast, x))
    end
end
NodeType(::Type{ADMatrix}) = Inner()
children(x::ADMatrix) = vcat(x.x)
compute_inner(x::ADMatrix, call) = map(call, x.x)
function backward(n::ADMatrix, vals, derivs)
    for i in CartesianIndices(n.x)
        add_deriv(derivs, n.x[i], derivs[n][i])
    end
end
Base.:(+)(::AbstractMatrix{<:ADNode}, ::Any) = error("Lift to ADMatrix for performance")
Base.:(+)(::Any, ::AbstractMatrix{<:ADNode}) = error("Lift to ADMatrix for performance")
Base.:(*)(::AbstractMatrix{<:ADNode}, ::AbstractMatrix) = error("Lift to ADMatrix for performance")
Base.:(*)(::AbstractMatrix, ::AbstractMatrix{<:ADNode}) = error("Lift to ADMatrix for performance")

struct GetIndex <: ADNode
    x::ADNode
    i::CartesianIndex
end
NodeType(::Type{GetIndex}) = Inner()
children(x::GetIndex) = [x.x]
compute_inner(x::GetIndex, call) = call(x.x)[x.i]
function backward(n::GetIndex, vals, derivs)
    if !haskey(derivs, n.x)
        derivs[n.x] = zero(vals[n.x])
    end
    derivs[n.x][n.i] += derivs[n]
end
Base.getindex(x::ADNode, i...) = GetIndex(x, CartesianIndex(i...))

# rtjoa: This could be more elegant (e.g. not require the user to provide the
# derivative of `f`) if we restructured autodiff.jl to be pure.
# One possible interface is:
#   `lambda(parameters::Vector{Var}, result::ADNode)::ADFunction`
#   `apply(f::ADFunction, arguments::Vector{ADNode})`
#   `compute(f::ADFunction, arguments::Vector{RM})::RM`
#     where `RM = Union{Real, AbstractMatrix}`
#   `differentiate(f::ADFunction)::ADFunction`
# ...but let's save this for the next Dice rewrite!
struct Map <: ADNode
    f::Function
    f′::Function
    x::ADNode
end
NodeType(::Type{Map}) = Inner()
children(x::Map) = x.x
compute_inner(x::Map, call) = map(x.f, call(x.x))
function backward(n::Map, vals, derivs)
    add_deriv(derivs, n.x, derivs[n] .* n.f′.(vals[n]))
end
ad_map(f::Function, f′::Function, x::ADNode) = Map(f, f′, x)

struct Transpose <: ADNode
    x::ADNode
end
NodeType(::Type{Transpose}) = Inner()
children(x::Transpose) = x.x
compute_inner(x::Transpose, call) = transpose(call(x.x))
function backward(n::Transpose, vals, derivs)
    add_deriv(derivs, n.x, transpose(derivs[n]))
end

# Desugared ops
Base.zero(::ADNode) = Constant(0)
Base.:(-)(x::ADNode) = x * -1
Base.:(-)(x::ADNode, y::ADNode) = x + -y
Base.:(-)(x::ADNode, y::ADNodeCompatible) = x + Constant(-y) 
Base.:(-)(x::ADNodeCompatible, y::ADNode) = Constant(x) - y
inv(x::ADNode) = x ^ Constant(-1.)
Base.:(/)(x::ADNode, y::ADNode) = x * inv(y)
Base.:(/)(x::ADNode, y::ADNodeCompatible) = x / Constant(y)
Base.:(/)(x::ADNodeCompatible, y::ADNode) = Constant(x) / y
Base.exp(x::ADNode) = ℯ ^ x
Base.abs(x::ADNode) = (x ^ 2) ^ (1/2)

sigmoid(x) = 1 / (1 + exp(-x))
deriv_sigmoid(x) = sigmoid(x) * (1 - sigmoid(x))
inverse_sigmoid(x) = log(x / (1 - x))