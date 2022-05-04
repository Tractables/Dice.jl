################################################
# DistBool definitions that do not use a manager
################################################

abstract type DistBool end

const AnyBool = Union{DistBool, Bool}

mutable struct Flip <: DistBool end
flip() = Flip()
flip()

struct DistAnd <: DistBool 
    conjuncts::Vector{DistBool}
end
Base.:(&)(xs::DistBool...) = DistAnd(collect(xs))
Base.:(&)(x::DistBool, y::Bool) = y ? x : false
Base.:(&)(x::Bool, y::DistBool) = y & x

flip() & flip()
true & flip()

struct DistOr <: DistBool 
    disjuncts::Vector{DistBool}
end
Base.:(|)(xs::DistBool...) = DistOr(collect(xs))
Base.:(|)(x::DistBool, y::Bool) = y ? true : x
Base.:(|)(x::Bool, y::DistBool) = y | x

flip() | flip()
false | flip()

struct DistNot <: DistBool
    b::DistBool
end
Base.:(!)(x::DistBool) = DistNot(x)
!flip()

(true & flip() & !flip()) | flip() | false

Base.:(==)(x::AnyBool, y::AnyBool) = (x & y) | (!x & !y) # should be a specialized operator?
Base.isless(x::AnyBool, y::AnyBool) = !x | y

flip() == flip()
isequal(flip(),flip())
flip() < flip()
flip() <= flip()

################################################
# DistInt definitions that do not use a manager
################################################

mutable struct DistInt
    bits::Vector{AnyBool}
end

numbits(x::DistInt) = length(x.bits)

function uniform(n,k) 
    @assert n >= k >= 0
    DistInt([i <= n-k ? false : flip() for i=1:n])
end

uniform(3,2)

Base.:(==)(x::DistInt, y::DistInt) = 
    mapreduce(==, &, x.bits, y.bits)

uniform(3,2) == uniform(3,2)

function Base.isless(x::DistInt, y::DistInt)
    @assert numbits(x) == numbits(y)
    foldr(zip(x.bits,y.bits); init=false) do bits, tail_isless
        xbit, ybit = bits
        (xbit < ybit) | (xbit == ybit) & tail_isless
    end
end

isless(uniform(3,2), uniform(3,2))

atleast_two(x,y,z) = (x & y) | (x & z) | (y & z)

function Base.:(+)(x::DistInt, y::DistInt)
    @assert numbits(x) == numbits(y)
    z = Vector{AnyBool}(undef, numbits(x))
    carry = false
    for i=numbits(x):-1:1
        z[i] = ((x.bits[i] != y.bits[i]) != carry)
        carry = atleast_two(x.bits[i], y.bits[i], carry)
    end
    if carry isa DistBool
        error("probabilistic integer overflow")
    elseif carry
        error("deterministic integer overflow")
    end
    DistInt(z)
end

uniform(2,1) + uniform(2,1)
DistInt([false,true]) + DistInt([false,true])
DistInt([true,true]) + DistInt([true,true])
uniform(2,2) + uniform(2,2)
uniform(3,2) + uniform(3,2)


################################################
# DSL magic playground
################################################

using IRTools

f() = (flip() & flip())
@code_ir f() 

f() = uniform(2,2) + uniform(2,2)
@code_ir f() 
@code_ir uniform(2,2) + uniform(2,2)

# TODO
# - transform IR to handle `error` with probabilistic path condition
# - transform IR to support `observe`
# - reusing of IR with free variables (e.g., for `atleast_two`)
# - sugar using standard Julia random API