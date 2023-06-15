
using DirectedAcyclicGraphs
using DataStructures: DefaultDict


abstract type ADNode <: DAG end

_parameter_to_value = Dict{Parameter, Float64}()

struct Parameter <: ADNode
    name::String
end
NodeType(::Type{Parameter}) = Leaf()

struct Constant <: ADNode
    value::Real
end
NodeType(::Type{Constant}) = Leaf()

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
 
struct Exp <: ADNode
    x::ADNode
    x::ADNode
end
NodeType(::Type{Exp}) = Inner()
children(x::Exp) = [x.x, x.y]
Base.:(^)(x::ADNode, y::ADNode) = Exp(x, y)
Base.:(^)(x::ADNode, y::Real) = Exp(x, Constant(y))
Base.:(^)(x::Real, y::ADNode) = Exp(Constant(x), y)

# Desugared ops
Base.:(-)(x::ADNode) = x * -1
Base.:(-)(x::ADNode, y::ADNode) = x + -y
Base.:(-)(x::ADNode, y::Real) = x + Constant(-y)
Base.:(-)(x::Real, y::ADNode) = Constant(x) - y
Base.:(/)(x::ADNode, y::ADNode) = x * (y ^ -1)
Base.:(/)(x::ADNode, y::Real) = x / Constant(y)
Base.:(/)(x::Real, y::ADNode) = Constant(x) / y

struct Log <: ADNode
    x::ADNode
end
NodeType(::Type{Log}) = Inner()
children(x::Log) = [x.x]
Base.log(x::ADNode) = Log(x)

function compute(roots::Vector{ADNode})
    values = Dict()

    fl(x::Parameter) = _parameter_to_value[x]
    fl(x::Constant) = x.value
    fi(x::Add, call) = call(x.x) + call(x.y)
    fi(x::Mul, call) = call(x.x) * call(x.y)
    fi(x::Exp, call) = call(x.x) ^ call(x.y)

    for root in roots
        haskey(values, root) || foldup(root, fl, fi, Float, values)
    end
    values
end

function diff(root_diffs::Dict{ADNode, Float})
    values = compute(collect(keys(root_diffs)))
    derivs = DefaultDict{ADNode, Float64}(0.)
    merge!(deriv, root_diffs)
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
    function f(n::Exp)
        deriv[n.x] += derivs[n] * values[n.y] * values[n.x] ^ (values[n.y] -1)
        deriv[n.y] += derivs[n] * log(values[n.y]) * values[n.x] ^ values[n.y]
    end
    foreach_down(f, keys(root_diffs))
    deriv
end

# Extending DirectedAcyclicGraphs.jl
function foreach_down(f::Function, roots::Vector{DAG})
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
