
export DistInt, DistInt8, DistInt16, DistInt32, unsigned_abs

##################################
# types, structs, and constructors
##################################

"A signed random W-bit integer in two's complement"
struct DistInt{W} <: Dist{Int}
    number::DistUInt{W}
end

function DistInt{W}(b::AbstractVector) where W
    DistInt{W}(DistUInt{W}(b))
end

function DistInt{W}(x::Int) where W
    @assert -(2^(W-1)) <= x < 2^(W-1) "Number $x cannot be represented by a `DistInt{$W}`"
    unsignedx = ifelse(x >= 0, x, x+2^W)
    DistInt{W}(DistUInt{W}(unsignedx))
end

const DistInt8 = DistInt{8}
const DistInt16 = DistInt{16}
const DistInt32= DistInt{32}

DistInt(x::Int) = DistInt16(x::Int)

function uniform(::Type{DistInt{W}}, n = W) where W
    DistInt{W}(uniform(DistUInt{W}, n).bits)
end

function uniform(::Type{DistInt{W}}, start::Int, stop::Int; kwargs...) where W
    @assert -(2^(W - 1)) <= start < stop <= (2^(W - 1))
    xoff = uniform(DistUInt{W+1}, 0, stop-start; kwargs...)
    x = DistInt{W+1}(xoff) + DistInt{W+1}(start)
    return convert(DistInt{W}, x)
end

# Generates a triangle on positive part of the support
function triangle(t::Type{DistInt{W}}, b::Int) where W
    @assert b < W
    DistInt(triangle(DistUInt{W}, b))
end

function Base.convert(::Type{T}, x::DistUInt{W1}) where T <: DistInt where W1
    convert(T, DistInt{W1+1}(x))
end

function Base.convert(::Type{DistInt{W2}}, x::DistInt{W1}) where W1 where W2
    bits = x.number.bits
    if W1 <= W2
        DistInt{W2}(vcat(fill(bits[1], W2 - W1), bits))
    else
        if errorcheck()
            err = any(b -> !prob_equals(b, bits[W1-W2+1]), bits[1:W1-W2])
            err && error("Cannot convert `DistInt` losslessly from bitwidth $W1 to $W2: $bits")
        end
        DistInt{W2}(bits[W1-W2+1:W1])
    end
end

##################################
# inference
##################################

tobits(x::DistInt) = tobits(x.number)

function frombits(x::DistInt{W}, world) where W
    base = frombits(signbit(x), world) ? -2^(W-1) : 0
    base + frombits(drop_bits(DistUInt{W-1}, x.number), world)
end

function expectation(x::DistInt{W}; kwargs...) where W
    bitprobs = pr(x.number.bits...; kwargs...)
    base = -(2^(W-1)) * bitprobs[1][true]
    base + expectation(bitprobs[2:end])
end

function variance(x::DistInt{W}; kwargs...) where W
    probs = variance_probs(x.number; kwargs...)
    ans = 0
    exponent1 = 1
    for i = 1:W
        ans += exponent1 * (probs[W+1-i, W+1-i] - probs[W+1-i, W+1-i]^2)
        exponent2 = exponent1*2
        for j = i+1:W
            exponent2 = 2*exponent2
            bi = probs[W+1-i, W+1-i]
            bj = probs[W+1-j, W+1-j]
            bibj = probs[W+1-i, W+1-j]
            if j == W
                ans -= exponent2 * (bibj - bi * bj)
            else
                ans += exponent2 * (bibj - bi * bj)
            end
        end
        exponent1 = exponent1*4
    end
    return ans
end

##################################
# methods
##################################

bitwidth(::DistInt{W}) where W = W

function prob_equals(x::DistInt{W}, y::DistInt{W}) where W
    prob_equals(x.number, y.number)
end

function Base.isless(x::DistInt{W}, y::DistInt{W}) where W
    ifelse(signbit(x) & !signbit(y), 
        true, 
        ifelse(!signbit(x) & signbit(y), 
            false, 
            isless(DistUInt{W-1}(x.number.bits[2:W]), DistUInt{W-1}(y.number.bits[2:W]))
        )
    )
end

function Base.ifelse(cond::Dist{Bool}, then::DistInt{W}, elze::DistInt{W}) where W
    DistInt{W}(ifelse(cond, then.number, elze.number))
end

"Compute the absolute value of a `DistInt{W}` as a `DistUInt{W}`"
function unsigned_abs(x::DistInt{W}) where W
    xp = ifelse(signbit(x), ~x.number, x.number)
    xpadd = ifelse(signbit(x), one(DistUInt{W}), zero(DistUInt{W}))
    xp + xpadd
end

Base.signbit(x::DistInt) = 
    x.number.bits[1]

function drop_bits(::Type{DistInt{W}}, x::DistInt) where W
    DistInt{W}(drop_bits(DistUInt{W}, x.number))
end

function Base.:(+)(x::DistInt{W}, y::DistInt{W}) where W
    z = convert(DistUInt{W+1}, x.number) + convert(DistUInt{W+1}, y.number)
    if errorcheck()
        overflow = ((!signbit(x) & !signbit(y) &  z.bits[2]) | 
                    ( signbit(x) &  signbit(y) & !z.bits[2]))
        overflow && error("integer overflow or underflow")
    end
    DistInt{W}(drop_bits(DistUInt{W}, z))
end

function Base.:(-)(x::DistInt{W}) where W
    errorcheck() & prob_equals(x, DistInt{W}(-2^(W-1))) && error("integer overflow in `-$x`")
    DistInt{W}(overflow_sum(~x.number, one(DistUInt{W})))
end

function Base.:(-)(x::DistInt{W}, y::DistInt{W}) where W
    z  = DistUInt{W+1}([true,  x.number.bits...]) 
    z -= DistUInt{W+1}([false, y.number.bits...])
    if errorcheck() 
        borrow = (!signbit(x) &  signbit(y) &  z.bits[2]) | 
                  (signbit(x) & !signbit(y) & !z.bits[2])
        borrow && error("integer overflow or underflow")
    end
    DistInt{W}(drop_bits(DistUInt{W},z))
end

function Base.:(*)(x::DistInt{W}, y::DistInt{W}) where W
    ux = convert(DistInt{2W}, x).number
    uy = convert(DistInt{2W}, y).number
    uz = zero(DistUInt{2W})
    for i = 2W:-1:1
        (i != 2W) && (ux <<= 1)
        added = ifelse(uy.bits[i], ux, zero(DistUInt{2W}))
        uz = overflow_sum(uz, added)
    end
    convert(DistInt{W}, DistInt{2W}(uz)) # there is an overflow check happening here
end

function Base.:(/)(x::DistInt{W}, y::DistInt{W}) where W
    if errorcheck()
        iszero(y) && error("division by zero")
        prob_equals(x, DistInt{W}(-2^(W-1))) & prob_equals(y, DistInt{W}(-1)) && error("integer overflow")
    end
    uz =  unsigned_abs(x) /  unsigned_abs(y)
    z = convert(DistInt{W+1}, uz) # increase bit width to represent abs of min value
    z = ifelse(xor(signbit(x), signbit(y)), -z, z)
    convert(DistInt{W}, z)
end

function Base.:(%)(x::DistInt{W}, y::DistInt{W}) where W
    errorcheck() & iszero(y) && error("division by zero")
    uz = unsigned_abs(x) % unsigned_abs(y)
    z = convert(DistInt{W}, uz)
    ifelse(signbit(x), -z, z)
end
