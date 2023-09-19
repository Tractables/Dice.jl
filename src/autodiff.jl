export var!, clear_vars!, value, compute, differentiate, step_maximize!,
    set_var!, sigmoid, add_unit_interval_var!, ADNode

using DirectedAcyclicGraphs
import DirectedAcyclicGraphs: NodeType, DAG, children
using DataStructures: DefaultDict

abstract type ADNode <: DAG end

struct Variable <: ADNode
    name::String
end
NodeType(::Type{Variable}) = Leaf()

_variable_to_value = Dict{Variable, Real}()

function var!(s, init_val, get_if_exists=true)
    var = Variable(s)
    if get_if_exists && haskey(_variable_to_value, var)
        return var
    end
    @assert !haskey(_variable_to_value, var)
    _variable_to_value[var] = init_val
    var
end


sigmoid(x) = 1 / (1 + exp(-x))
# deriv_sigmoid(x) = sigmoid(x) * (1 - sigmoid(x))
inverse_sigmoid(x) = log(x / (1 - x))

function add_unit_interval_var!(s, init_val=0.5, get_if_exists=true)
    @assert 0 < init_val < 1
    before_sigmoid = var!(
        "$(s)_before_sigmoid", inverse_sigmoid(init_val), get_if_exists
    )
    sigmoid(before_sigmoid)
end

function set_var_value!(var, value)
    _variable_to_value[var] = value
end

function clear_vars!()
    empty!(_variable_to_value)
end

struct Constant <: ADNode
    value::Real
end
NodeType(::Type{Constant}) = Leaf()
Base.zero(::ADNode) = Constant(0)

Base.show(io::IO, x::Variable) =  print(io, "Variable($(x.name))")
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

function compute(root, vals=nothing)
    isnothing(vals) && (vals = Dict{ADNode, Real}())

    fl(x::Variable) = _variable_to_value[x]
    fl(x::Constant) = x.value
    fi(x::Add, call) = call(x.x) + call(x.y)
    fi(x::Mul, call) = call(x.x) * call(x.y)
    fi(x::Pow, call) = call(x.x) ^ call(x.y)
    # fi(x::Div, call) = call(x.x) / call(x.y)
    fi(x::Log, call) = log(call(x.x))
    # fi(x::Exp, call) = exp(call(x.x))

    foldup(root, fl, fi, Real, vals)
end

function differentiate(root_derivs::AbstractDict{<:ADNode, <:Real})
    vals = Dict{ADNode, Real}()
    for root in keys(root_derivs)
        compute(root, vals)
    end
    
    derivs = DefaultDict{ADNode, Real}(0)
    merge!(derivs, root_derivs)
    f(::Constant) = nothing
    f(::Variable) = nothing
    function f(n::Add)
        derivs[n.x] += derivs[n]
        derivs[n.y] += derivs[n]
    end
    function f(n::Mul)
        derivs[n.x] += derivs[n] * vals[n.y]
        derivs[n.y] += derivs[n] * vals[n.x]
    end
    # function f(n::Div)
    #     derivs[n.x] += derivs[n] / vals[n.y]
    #     derivs[n.y] -= derivs[n] * vals[n.x] / vals[n.y] ^ 2
    # end
    function f(n::Pow)
        derivs[n.x] += derivs[n] * vals[n.y] * vals[n.x] ^ (vals[n.y] - 1)
        if !(n.y isa Constant)
            derivs[n.y] += derivs[n] * log(vals[n.x]) * vals[n.x] ^ vals[n.y]
        end
    end
    function f(n::Log)
        derivs[n.x] += derivs[n] / vals[n.x]
    end
    # function f(n::Exp)
    #     derivs[n.x] += derivs[n] * exp(vals[n.x])
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

value(x::Variable) = _variable_to_value[x]

function step_maximize!(roots, learning_rate)
    root_derivs = Dict(
        root => 1
        for root in roots
    )
    derivs = differentiate(root_derivs)
    for (n, d) in derivs
        if n isa Variable
            _variable_to_value[n] += d * learning_rate
        end
    end
end
