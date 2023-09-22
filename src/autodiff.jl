export new_var!, clear_vars!, value, compute, differentiate, step_maximize!,
    set_var!, sigmoid, add_unit_interval_var!, ADNode, Var, train_vars!, value,
    ADMatrix, ad_map

using DirectedAcyclicGraphs
import DirectedAcyclicGraphs: NodeType, DAG, children
using DataStructures: DefaultDict

abstract type ADNode <: DAG end

ADNodeCompatible = Union{Real, AbstractMatrix{<:Real}}

struct Var <: ADNode
    name::String
end

NodeType(::Type{Var}) = Leaf()

_variable_to_value = Dict{String, ADNodeCompatible}()

function value(var::Var)
    _variable_to_value[var.name]
end

var_exists(s) = haskey(_variable_to_value, s)

function set_var!(s, val)
    _variable_to_value[s] = val
    Var(s)
end

function new_var!(s, init_val)
    @assert !var_exists(s)
    set_var!(s, init_val)
end

function get_or_init_var!(s, if_not_exists=nothing)
    if var_exists(s)
        Var(s)
    else
        set_var!(s, if_not_exists)
    end
end

sigmoid(x) = 1 / (1 + exp(-x))
deriv_sigmoid(x) = sigmoid(x) * (1 - sigmoid(x))
inverse_sigmoid(x) = log(x / (1 - x))


function add_unit_interval_var!(s, init_val=0.5)
    @assert 0 < init_val < 1
    before_sigmoid = get_or_init_var!(
        "$(s)_before_sigmoid", inverse_sigmoid(init_val)
    )
    sigmoid(before_sigmoid)
end

function clear_vars!()
    empty!(_variable_to_value)
end

struct Constant <: ADNode
    value::ADNodeCompatible
end
NodeType(::Type{Constant}) = Leaf()
Base.zero(::ADNode) = Constant(0)

Base.show(io::IO, x::Var) =
    print(io, "Var($(x.name))")
Base.show(io::IO, x::Constant) =
    print(io, "Constant($(x.value))")

struct Add <: ADNode
    x::ADNode
    y::ADNode
end
NodeType(::Type{Add}) = Inner()
children(x::Add) = [x.x, x.y]
Base.:(+)(x::ADNode, y::ADNode) = Add(x, y)
Base.:(+)(x::ADNode, y::ADNodeCompatible) = Add(x, Constant(y))
Base.:(+)(x::ADNodeCompatible, y::ADNode) = Add(Constant(x), y)

struct Mul <: ADNode
    x::ADNode
    y::ADNode
end
NodeType(::Type{Mul}) = Inner()
children(x::Mul) = [x.x, x.y]
Base.:(*)(x::ADNode, y::ADNode) = Mul(x, y)
Base.:(*)(x::ADNode, y::ADNodeCompatible) = Mul(x, Constant(y))
Base.:(*)(x::ADNodeCompatible, y::ADNode) = Mul(Constant(x), y)

# struct Div <: ADNode
#     x::ADNode
#     y::ADNode
# end
# NodeType(::Type{Div}) = Inner()
# children(x::Div) = [x.x, x.y]
# Base.:(/)(x::ADNode, y::ADNode) = Div(x, y)
# Base.:(/)(x::ADNode, y::Real) = Div(x, Constant(y))
# Base.:(/)(x::Real, y::ADNode) = Div(Constant(x), y)

struct Pow <: ADNode
    x::ADNode
    y::ADNode
end
NodeType(::Type{Pow}) = Inner()
children(x::Pow) = [x.x, x.y]

Base.:(^)(x::ADNode, y::ADNode) = Pow(x, y)
Base.:(^)(x::ADNode, y::ADNodeCompatible) = Pow(x, Constant(y))
Base.:(^)(x::ADNodeCompatible, y::ADNode) = Pow(Constant(x), y)

struct Sin <: ADNode
    x::ADNode
end
NodeType(::Type{Sin}) = Inner()
children(x::Sin) = [x.x]

Base.sin(x::ADNode) = Sin(x)

struct Cos <: ADNode
    x::ADNode
end
NodeType(::Type{Cos}) = Inner()
children(x::Cos) = [x.x]

Base.cos(x::ADNode) = Cos(x)

# struct Exp <: ADNode
#     x::ADNode
# end
# NodeType(::Type{Exp}) = Inner()
# children(x::Exp) = [x.x]
# Base.exp(x::ADNode) = Exp(x)

# Desugared ops
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

struct Log <: ADNode
    x::ADNode
end
NodeType(::Type{Log}) = Inner()
children(x::Log) = [x.x]
Base.log(x::ADNode) = Log(x)

# Matrix ops

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
ad_map(f::Function, f′::Function, x::ADNode) = Map(f, f′, x)


struct Transpose <: ADNode
    x::ADNode
end
NodeType(::Type{Transpose}) = Inner()
children(x::Transpose) = x.x

function compute(root, vals=nothing)
    isnothing(vals) && (vals = Dict{ADNode, Any}())

    fl(x::Var) = value(x)
    fl(x::Constant) = x.value
    fi(x::Add, call) = call(x.x) + call(x.y)
    fi(x::Mul, call) = call(x.x) * call(x.y)
    fi(x::Pow, call) = call(x.x) ^ call(x.y)
    # fi(x::Div, call) = call(x.x) / call(x.y)
    fi(x::Log, call) = log(call(x.x))
    # fi(x::Exp, call) = exp(call(x.x))
    fi(x::Sin, call) = sin(call(x.x))
    fi(x::Cos, call) = cos(call(x.x))
    fi(x::GetIndex, call) = call(x.x)[x.i]
    fi(x::ADMatrix, call) = map(call, x.x)
    fi(x::Map, call) = map(x.f, call(x.x))
    fi(x::Transpose, call) = transpose(call(x.x))

    foldup(root, fl, fi, ADNodeCompatible, vals)
end

function differentiate(root_derivs::AbstractDict{<:ADNode, <:ADNodeCompatible})
    vals = Dict{ADNode, ADNodeCompatible}()
    for root in keys(root_derivs)
        compute(root, vals)
    end
    
    derivs = Dict{ADNode, ADNodeCompatible}()
    merge!(derivs, root_derivs)
    f(::Constant) = nothing
    f(::Var) = nothing
    function add_deriv(n::ADNode, amount::ADNodeCompatible)
        if haskey(derivs, n)
            derivs[n] += amount
        else
            derivs[n] = amount
        end
    end
    function f(n::Add)
        add_deriv(n.x, derivs[n])
        add_deriv(n.y, derivs[n])
    end
    function f(n::Mul)
        if derivs[n] isa Real
            add_deriv(n.x, derivs[n] * vals[n.y])
            add_deriv(n.y, derivs[n] * vals[n.x])
        elseif derivs[n] isa AbstractMatrix{<:Real}
            add_deriv(n.x, derivs[n] * transpose(vals[n.y]))
            add_deriv(n.y, transpose(vals[n.x]) * derivs[n])
        else
            error("bad derivs type")
        end
    end
    # function f(n::Div)
    #     derivs[n.x] += derivs[n] / vals[n.y]
    #     derivs[n.y] -= derivs[n] * vals[n.x] / vals[n.y] ^ 2
    # end
    function f(n::Pow)
        @assert derivs[n] isa Real
        add_deriv(n.x, derivs[n] * vals[n.y] * vals[n.x] ^ (vals[n.y] - 1))
        if !(n.y isa Constant)
            add_deriv(n.y, derivs[n] * log(vals[n.x]) * vals[n.x] ^ vals[n.y])
        end
    end
    function f(n::Log)
        @assert derivs[n] isa Real
        add_deriv(n.x, derivs[n] / vals[n.x])
    end
    function f(n::Sin)
        @assert derivs[n] isa Real
        add_deriv(n.x, derivs[n] * cos(vals[n.x]))
    end
    function f(n::Cos)
        @assert derivs[n] isa Real
        add_deriv(n.x, derivs[n] * -sin(vals[n.x]))
    end
    function f(n::ADMatrix)
        for i in CartesianIndices(n.x)
            add_deriv(n.x[i], derivs[n][i])
        end
    end
    function f(n::GetIndex)
        if !haskey(derivs, n.x)
            derivs[n.x] = zero(vals[n.x])
        end
        derivs[n.x][n.i] += derivs[n]
    end
    function f(n::Map)
        add_deriv(n.x, derivs[n] .* n.f′.(vals[n]))
    end
    function f(n::Transpose)
        add_deriv(n.x, transpose(derivs[n]))
    end


    # function f(n::Exp)
    #     derivs[n.x] += derivs[n] * exp(vals[n.x])
    # end
    foreach_down(n -> if haskey(derivs, n) f(n) end, keys(root_derivs))
    derivs
end

# Extending DirectedAcyclicGraphs.jl
function foreach_down(f::Function, roots)
    seen = Set()
    rev_topo = []
    function visit(n)
        n ∈ seen && return
        push!(seen, n)
        if isinner(n)
            for child in children(n)
                visit(child)
            end
        end
        push!(rev_topo, n)
    end
    for root in roots
        visit(root)
    end

    for n in Iterators.reverse(rev_topo)
        f(n)
    end
end

function step_maximize!(roots, learning_rate)
    root_derivs = Dict(
        root => 1
        for root in roots
    )
    derivs = differentiate(root_derivs)
    for (n, d) in derivs
        if n isa Var
            _variable_to_value[n.name] += d * learning_rate
        end
    end
end

function train_vars!(
    x::ADNode,
    epochs::Integer=2000,
    learning_rate::AbstractFloat=0.003,
)
    for _ in 1:epochs
        step_maximize!([x], learning_rate)
    end
end
