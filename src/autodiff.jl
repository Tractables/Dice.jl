export add_param!, clear_params!, value, compute, differentiate, step_maximize!

using DirectedAcyclicGraphs
import DirectedAcyclicGraphs: NodeType
using DataStructures: DefaultDict

abstract type ADNode <: DAG end

struct Parameter <: ADNode
    name::String
end
NodeType(::Type{Parameter}) = Leaf()

_parameter_to_value = Dict{Parameter, Real}()

function add_param!(s, value)
    param = Parameter(s)
    @assert !haskey(_parameter_to_value, param)
    _parameter_to_value[param] = value
    param
end

function clear_params!()
    empty!(_parameter_to_value)
end

struct Constant <: ADNode
    value::Real
end
NodeType(::Type{Constant}) = Leaf()

Base.show(io::IO, x::Parameter) =  print(io, "Parameter($(x.name))")
Base.show(io::IO, x::Constant) = print(io, "Constant($(x.value))")

struct Add <: ADNode
    x::ADNode
    y::ADNode
end
NodeType(::Type{Add}) = Inner()
children(x::Add) = [x.x, x.y]
Base.:(+)(x::ADNode, y::ADNode) = Add(x, y)
Base.:(+)(x::ADNode, y::Real) = Add(x, Constant(y))
Base.:(+)(x::Real, y::ADNode) = Add(Constant(x), y)

struct Mul <: ADNode
    x::ADNode
    y::ADNode
end
NodeType(::Type{Mul}) = Inner()
children(x::Mul) = [x.x, x.y]
Base.:(*)(x::ADNode, y::ADNode) = Mul(x, y)
Base.:(*)(x::ADNode, y::Real) = Mul(x, Constant(y))
Base.:(*)(x::Real, y::ADNode) = Mul(Constant(x), y)

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
Base.:(^)(x::ADNode, y::Real) = Pow(x, Constant(y))
Base.:(^)(x::Real, y::ADNode) = Pow(Constant(x), y)

# struct Exp <: ADNode
#     x::ADNode
# end
# NodeType(::Type{Exp}) = Inner()
# children(x::Exp) = [x.x]
# Base.exp(x::ADNode) = Exp(x)

# Desugared ops
Base.:(-)(x::ADNode) = x * -1
Base.:(-)(x::ADNode, y::ADNode) = x + -y
Base.:(-)(x::ADNode, y::Real) = x + Constant(-y)
Base.:(-)(x::Real, y::ADNode) = Constant(x) - y
Base.:(/)(x::ADNode, y::ADNode) = x * Pow(y, Constant(-1.))
Base.:(/)(x::ADNode, y::Real) = x / Constant(y)
Base.:(/)(x::Real, y::ADNode) = Constant(x) / y
Base.exp(x::ADNode) = ℯ ^ x
Base.abs(x::ADNode) = (x ^ 2) ^ (1/2)

struct Log <: ADNode
    x::ADNode
end
NodeType(::Type{Log}) = Inner()
children(x::Log) = [x.x]
Base.log(x::ADNode) = Log(x)

function compute(roots::Vector{<:ADNode})
    values = Dict{ADNode, Real}()

    fl(x::Parameter) = _parameter_to_value[x]
    fl(x::Constant) = x.value
    fi(x::Add, call) = call(x.x) + call(x.y)
    fi(x::Mul, call) = call(x.x) * call(x.y)
    fi(x::Pow, call) = call(x.x) ^ call(x.y)
    # fi(x::Div, call) = call(x.x) / call(x.y)
    fi(x::Log, call) = log(call(x.x))
    # fi(x::Exp, call) = exp(call(x.x))

    for root in roots
        haskey(values, root) || foldup(root, fl, fi, Real, values)
    end
    values
end

function differentiate(root_derivs::Dict{<:ADNode, <:Real})
    values = compute(collect(keys(root_derivs)))
    derivs = DefaultDict{ADNode, Real}(0)
    merge!(derivs, root_derivs)
    f(::Constant) = nothing
    f(::Parameter) = nothing
    function f(n::Add)
        derivs[n.x] += derivs[n]
        derivs[n.y] += derivs[n]
    end
    function f(n::Mul)
        derivs[n.x] += derivs[n] * values[n.y]
        derivs[n.y] += derivs[n] * values[n.x]
    end
    # function f(n::Div)
    #     derivs[n.x] += derivs[n] / values[n.y]
    #     derivs[n.y] -= derivs[n] * values[n.x] / values[n.y] ^ 2
    # end
    function f(n::Pow)
        derivs[n.x] += derivs[n] * values[n.y] * values[n.x] ^ (values[n.y] - 1)
        if !(n.y isa Constant)
            derivs[n.y] += derivs[n] * log(values[n.x]) * values[n.x] ^ values[n.y]
        end
    end
    function f(n::Log)
        derivs[n.x] += derivs[n] / values[n.x]
    end
    # function f(n::Exp)
    #     derivs[n.x] += derivs[n] * exp(values[n.x])
    # end
    foreach_down(f, keys(root_derivs))
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

value(x::Parameter) = _parameter_to_value[x]

function step_maximize!(roots, learning_rate)
    root_derivs = Dict(
        root => 1
        for root in roots
    )
    derivs = differentiate(root_derivs)
    for (n, d) in derivs
        if n isa Parameter
            _parameter_to_value[n] += d * learning_rate
        end
    end
end