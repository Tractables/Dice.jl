
export DistInt, uniform

##################################
# types, structs, and constructors
##################################

struct DistInt{W} <: Dist{Int}
    # first index is most significant bit
    bits::Vector{AnyBool}
    function DistInt{W}(b) where W
        @assert length(b) == W
        @assert W <= 63
        new{W}(b)
    end
end

DistInt(b) = DistInt{length(b)}(b)

##################################
# inference
##################################

tobits(x::DistInt) = 
    filter(y -> y isa Dist{Bool}, x.bits)

function frombits(x::DistInt{W}, world) where W
    v = 0
    for i = 1:W
        if frombits(x.bits[i], world)
            v += 2^(W-i)
        end
    end
    v
end

##################################
# methods
##################################

bitwidth(::DistInt{W}) where W = W

function uniform(::Type{DistInt{W}}, n = W) where W
    @assert W >= n >= 0
    DistInt{W}([i > W-n ? flip(0.5) : false for i=1:W])
end

##################################
# other method overloading
##################################

function prob_equals(x::DistInt{W}, y::DistInt{W}) where W
    mapreduce(prob_equals, &, x.bits, y.bits)
end

function Base.isless(x::DistInt{W}, y::DistInt{W}) where W
    foldr(zip(x.bits,y.bits); init=false) do bits, tail_isless
        xbit, ybit = bits
        (xbit < ybit) | (xbit == ybit) & tail_isless
    end
end

function Base.:(+)(x::DistInt{W}, y::DistInt{W}) where W
    z = Vector{AnyBool}(undef, W)
    carry = false
    for i=W:-1:1
        z[i] = xor(x.bits[i], y.bits[i], carry)
        carry = atleast_two(x.bits[i], y.bits[i], carry)
    end
    carry && error("integer overflow")
    DistInt{W}(z)
end

# Base.isless(x::AnyBool, y::AnyBool) = !x & y

# prob_equals(x::Bool, y::Bool) = x == y
# prob_equals(x::Bool, y::Dist{Bool}) = x ? y : !y
# prob_equals(x::Dist{Bool}, y::Bool) = prob_equals(y,x)
# prob_equals(x::Dist{Bool}, y::Dist{Bool}) = 
#     x == y ? true : (x & y) | (!x & !y)

# function ifelse(cond::Dist{Bool}, then::AnyBool, elze::AnyBool)
#     (then == elze) && return then
#     (cond == then) && return cond | elze
#     (cond == elze) && return cond & then
#     # TODO special case some DistNot branches
#     (cond & then) | (!cond & elze)
# end
  