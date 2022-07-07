
export flip, prob_equals

##################################
# types, structs, and constructors
##################################

const AnyBool = Union{Dist{Bool}, Bool}

abstract type DistBoolOp <: Dist{Bool} end

mutable struct DistAnd <: DistBoolOp
    x::Dist{Bool}
    y::Dist{Bool}
end

Base.:(&)(x::Dist{Bool}, y::Dist{Bool}) = x == y ? x : DistAnd(x,y)
Base.:(&)(x::Dist{Bool}, y::Bool) = y ? x : false
Base.:(&)(x::Bool, y::Dist{Bool}) = y & x

mutable struct DistOr <: DistBoolOp
    x::Dist{Bool}
    y::Dist{Bool}
end

Base.:(|)(x::Dist{Bool}, y::Dist{Bool}) = x == y ? x : DistOr(x,y)
Base.:(|)(x::Dist{Bool}, y::Bool) = y ? true : x
Base.:(|)(x::Bool, y::Dist{Bool}) = y | x

# TODO could be mutable or immutable? see how performance is impacted
struct DistNot <: DistBoolOp
    x::Dist{Bool}
end

Base.:(!)(x::Dist{Bool}) = DistNot(x)
Base.:(!)(y::DistNot) = y.x

# TODO should become and atomic int when we care about multithreading
global_flip_id = one(Int64)

struct Flip <: Dist{Bool}
    global_id::Int
    prob
    Flip(p) = begin
        @assert !iszero(p) && !isone(p) "Use `true` and `false` for deterministic flips"
        global global_flip_id
        new(global_flip_id += 1, p)
    end
end

"Create a Bernoulli random variable with the given probability (a coin flip)"
function flip(prob)
    iszero(prob) && return false
    isone(prob) && return true
    Flip(prob)
end

##################################
# DirectedAcyclicGraphs.jl
##################################

NodeType(::Type{<:DistBoolOp}) = Inner()
NodeType(::Type{<:Flip}) = Leaf()

children(z::DistAnd) = [z.x, z.y]
children(z::DistOr) = [z.x, z.y]
children(z::DistNot) = [z.x]
children(::Flip) = []

##################################
# inference
##################################

pr(x::Bool, ::InferAlgo) = pr(x)
pr(x::Bool) = x ? 1.0 : 0.0

##################################
# other method overloading
##################################

Base.isless(x::AnyBool, y::AnyBool) = !x & y

prob_equals(x::Bool, y::Bool) = x == y
prob_equals(x::Bool, y::Dist{Bool}) = x ? y : !y
prob_equals(x::Dist{Bool}, y::Bool) = prob_equals(y,x)
prob_equals(x::Dist{Bool}, y::Dist{Bool}) = 
    x == y ? true : (x & y) | (!x & !y)

function ifelse(cond::Dist{Bool}, then::AnyBool, elze::AnyBool)
    (then == elze) && return then
    (cond == then) && return cond | elze
    (cond == elze) && return cond & then
    # TODO special case some DistNot branches
    (cond & then) | (!cond & elze)
end
  