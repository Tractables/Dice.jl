
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

function DistInt{W}(i::Int) where W
    @assert i >= 0
    num_b = ndigits(i, base = 2)
    bits = Vector{AnyBool}(undef, W)
    for bit_idx = W:-1:1
        bits[bit_idx] = (bit_idx > W - num_b) ? Bool(i & 1) : false
        i = i >> 1
    end
    DistInt{W}(bits)
end

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

function Base.:(-)(x::DistInt{W}, y::DistInt{W}) where W
    z = Vector{AnyBool}(undef, W)
    borrow = false
    for i=W:-1:1
        z[i] = xor(x.bits[i], y.bits[i], borrow)
        borrow = ifelse(borrow, !x.bits[i] | y.bits[i], !x.bits[i] & y.bits[i])
    end
    borrow && error("integer overflow")
    DistInt{W}(z)
end

function ifelse(cond::Dist{Bool}, then::DistInt{W}, elze::DistInt{W}) where W
    (then == elze) && return then
    bits = map(then.bits, elze.bits) do tb, eb
        ifelse(cond, tb, eb)
    end
    DistInt{W}(bits)
end
  