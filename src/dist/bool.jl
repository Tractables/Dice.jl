
export flip, prob_equals, AnyBool, expectation, variance, foreach_node, flip_prob!

##################################
# types, structs, and constructors
##################################

const AnyBool = Union{Dist{Bool}, Bool}

# TODO should become an atomic int when we care about multithreading
global_flip_id::Int64 = one(Int64)
    # number field on 'sampling branch'

# Compilation into wbf
#   The struct def for constructing a new Boolean variable f with the given probability
#       so you can assign f = Flip(0.6, "x") --> f is a new probabilistic Boolean variable 
mutable struct Flip <: Dist{Bool}
    const global_id::Int
    prob
    const name
    ## NEW ## - note that bit_index 0 = MSB
    bit_index::Union{Nothing, Int}
    ordering::Int
    ## End NEW ##
    
    Flip(prob, name, bit_index) = begin
        if prob isa Real
            @assert !isone(prob) "Use `true` for deterministic flips"
            @assert !iszero(prob) "Use `false` for deterministic flips"
            @assert isnan(prob) || 0 < prob < 1 "Probabilities are between 0 and 1 (or undefined as NaN)"
        end
        global global_flip_id
        id = global_flip_id+=1
        new(id, prob, name, bit_index, id)
    end
end

# Modified SHOW to include orderings
function Base.show(io::IO, f::Flip)
    p = f.prob
    p = if p isa AbstractFloat round(p, digits=2) else p end
    if isnothing(f.name)
        print(io, "$(typeof(f))($(f.global_id),$(p), ordering=$(f.ordering)), bit_index=$(f.bit_index))")
    else
        print(io, "$(typeof(f))($(f.global_id),$(p),$(f.name), ordering=$(f.ordering)), bit_index=$(f.bit_index))")
    end
end

# function Base.show(io::IO, f::Flip)
#     p = f.prob
#     p = if p isa AbstractFloat round(p, digits=2) else p end
#     if isnothing(f.name)
#         print(io, "$(typeof(f))($(f.global_id),$(p))")
#     else
#         print(io, "$(typeof(f))($(f.global_id),$(p),$(f.name))")
#     end
# end

"Create a Bernoulli random variable with the given probability (a coin flip)"
#   C-FLIP (coin flip compilation)
#   (is returned from this function?)
function flip(prob = NaN16; name = nothing, bit_index = nothing)
    if prob isa Real
        iszero(prob) && return false
        isone(prob) && return true
    end
    Flip(prob, name, bit_index)
end

"Set the probability of a flip that has not been assigned a probability yet"
function flip_prob!(f::Flip, prob::Real)
    @assert isnan(f.prob)
    iszero(prob) && return false
    isone(prob) && return true
    @assert isnan(prob) || 0 < prob < 1 "Probabilities are between 0 and 1 (or undefined as NaN), not $prob"
    f.prob = prob
    f
end

abstract type DistBoolOp <: Dist{Bool} end
abstract type DistBoolBinOp <: DistBoolOp end

mutable struct DistAnd <: DistBoolBinOp
    const x::Dist{Bool}
    const y::Dist{Bool}
end

Base.:(&)(x::Dist{Bool}, y::Bool) = y ? x : false
Base.:(&)(x::Bool, y::Dist{Bool}) = y & x
function Base.:(&)(x::Dist{Bool}, y::Dist{Bool}) 
    # TODO figure out if we want `===` or `==` for these optimizations
    x == y && return x
    if (x isa DistBoolBinOp) && (y isa DistBoolBinOp) && 
            (x.x == y.x) && (x.y == y.y) # operand order is mostly fixed by hashcode
        (x isa DistAnd) && return x
        return y
    end
    DistAnd(x,y)
end

mutable struct DistOr <: DistBoolBinOp
    const x::Dist{Bool}
    const y::Dist{Bool}
end

Base.:(|)(x::Dist{Bool}, y::Bool) = y ? true : x
Base.:(|)(x::Bool, y::Dist{Bool}) = y | x
function Base.:(|)(x::Dist{Bool}, y::Dist{Bool}) 
    # TODO figure out if we want `===` or `==` for these optimizations
    x == y && return x
    if (x isa DistBoolBinOp) && (y isa DistBoolBinOp) && 
            (x.x == y.x) && (x.y == y.y) # operand order is mostly fixed by hashcode
        (x isa DistOr) && return x
        return y
    end
    DistOr(x,y)
end

# TODO could be mutable or immutable? see how performance is impacted
struct DistNot <: DistBoolOp
    x::Dist{Bool}
end

# aim to strip negations whenever possible
Base.:(!)(x::Dist{Bool}) = DistNot(x)
Base.:(!)(y::DistNot) = y.x

Base.:(&)(x::Dist{Bool}, y::DistNot) = x == !y ? false : DistAnd(x,y)
Base.:(&)(y::DistNot, x::Dist{Bool}) = x & y
Base.:(&)(x::DistNot, y::DistNot) = !((!x) | (!y))

Base.:(|)(x::Dist{Bool}, y::DistNot) = x == !y ? true : DistOr(x,y)
Base.:(|)(y::DistNot, x::Dist{Bool}) = x | y
Base.:(|)(x::DistNot, y::DistNot) = !((!x) & (!y))

##################################
# inference - function definitions
##################################

tobits(::Bool) = []
    # a plain Boolean value doesn't become probabilistic bits
tobits(b::Dist{Bool}) = [b]
    # takes in a Dist{Bool} object, which includes FLIPS
frombits(b::Bool, _) = b
    # Just returns boolean value itself
frombits(b::Dist{Bool}, world) = world[b]
frombits_as_dist(b::Dist{Bool}, world) = world[b]

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
# methods
##################################

# Handling OBSERVE statements (C-OBS)
#    (transforms observe aexp to (T, phi, theta)) --> condition on phi being true
#   somehow enforces that the 'observe' statements must be true
prob_equals(x::Bool, y::Bool) = x == y      # If x/y known booleans (ie they are 'true' or 'false)
prob_equals(x::Bool, y::Dist{Bool}) = x ? y : !y
prob_equals(x::Dist{Bool}, y::Bool) = prob_equals(y,x)
prob_equals(x::Dist{Bool}, y::Dist{Bool}) = 
    x == y ? true : (x & y) | (!x & !y)

"
chatGPT example: 
    f1 = flip(0.3)
    f2 = flip(0.6)
    observe(f1 == f2)
    f1 == f2 compiles to (phi, T, theta) where phi is the boolean formula 
        (f1 && f2) | (!f1 && !f2)
    applying C-OBS --> this becomes (T, phi, theta) --> all future computations must
        assume that f1 and f2 are equal
    ==> 'directly replaces equality checks w/ Boolean formulas

"

Base.xor(x::Bool, y::Dist{Bool}) = x ? !y : y
Base.xor(x::Dist{Bool}, y::Bool) = xor(y,x)
Base.xor(x::Dist{Bool}, y::Dist{Bool}) = 
    x == y ? false : (!x | !y) & (x | y)

Base.isless(x::AnyBool, y::AnyBool) = !x & y

Base.:(<=)(x::AnyBool, y::AnyBool) = !isless(y, x)
Base.:(>=)(x::AnyBool, y::AnyBool) = !isless(x, y)

# Compilation rule C-ITE        (if-then-else)
function Base.ifelse(cond::Dist{Bool}, then::AnyBool, elze::AnyBool)
    # Optimization cases
    (then == elze) && return then
    (cond == then) && return cond | elze
    (cond == elze) && return cond & then
    # TODO special case some DistNot branches
    # Regular case:
    (cond & then) | (!cond & elze)
end

"Test whether at least two of three arguments are true"
atleast_two(x,y,z) = (x & y) | ((x | y) & z)

# for C-LET compilation 
#   (recall: 'let' --> basically used to define vars to be used in later statements)
function foreach_node(f, roots)
    seen = Set{Dist{Bool}}()
    for root in roots
        root isa Bool && continue
        foreach(root) do node
            node ∈ seen && return
            push!(seen, node)
            f(node)
        end
    end
end

##################################
# inference
##################################

"Compute the expected value of a random variable"
expectation(x::AnyBool; kwargs...) = 
    pr(x; kwargs...)[true]

"Compute the variance of a random variable"
function variance(x::AnyBool; kwargs...)
    p = pr(x; kwargs...)
    p[true] * p[false]
end