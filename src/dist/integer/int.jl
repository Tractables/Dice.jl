
export DistInt, DistInt8, DistInt16, DistInt32, DistInt64, DistInt128

##################################
# types, structs, and constructors
##################################

struct DistInt{W} <: Dist{Int}
    number::DistUInt{W}
end

function DistInt{W}(b::AbstractVector) where W
    DistInt{W}(DistUInt{W}(b))
end

function DistInt{W}(i::Int) where W
    @assert i < 2^(W-1)
    @assert i >= -(2^(W-1))
    new_i = if i >= 0 i else i + 2^W end
    DistInt{W}(DistUInt{W}(new_i))
end

const DistInt8 = DistInt{8}
const DistInt16 = DistInt{16}
const DistInt32= DistInt{32}
const DistInt64 = DistInt{64}
const DistInt128 = DistInt{128}

##################################
# inference
##################################

tobits(x::DistInt) = tobits(x.number)

function frombits(x::DistInt{W}, world) where W
    v = frombits(x.number.bits[1], world) ? -2^(W-1) : 0
    for i = 2:W
        if frombits(x.number.bits[i], world)
            v += 2^(W-i)
        end
    end
    v
end

function expectation(x::DistInt{W}; kwargs...) where W
    prs = pr(x.number.bits...; kwargs...)
    ans = -(2^(W-1)) * prs[1][true]
    start = 2^(W-2)
    for i=2:W
        ans += start * prs[i][true]
        start /= 2
    end
    ans
end

##################################
# methods
##################################

bitwidth(::DistInt{W}) where W = W

function uniform(::Type{DistInt{W}}, n = W) where W
    DistInt{W}(uniform(DistUInt{W}, n).bits)
end

# Generates a triangle on positive part of the support
function triangle(t::Type{DistInt{W}}, b::Int) where W
    @assert b < W
    DistInt(triangle(DistUInt{W}, b))
end

##################################
# casting
##################################

function Base.convert(x::DistInt{W1}, t::Type{DistInt{W2}}) where W1 where W2
    if W1 <= W2
        DistInt{W2}(vcat(fill(x.number.bits[1], W2 - W1), x.number.bits))
    else
        #TODO: throw error if msb is not irrelevant
        DistInt{W2}(x.number.bits[W1 - W2 + 1:W1])
    end
end


# ##################################
# # other method overloading
# ##################################

function prob_equals(x::DistInt{W}, y::DistInt{W}) where W
    prob_equals(x.number, y.number)
end

function Base.ifelse(cond::Dist{Bool}, then::DistInt{W}, elze::DistInt{W}) where W
    DistInt{W}(ifelse(cond, then.number, elze.number))
end

function Base.:(+)(x::DistInt{W}, y::DistInt{W}) where W
    ans = convert(x.number, DistUInt{W+1}) + convert(y.number, DistUInt{W+1})
    carry = (!x.number.bits[1] & !y.number.bits[1] & ans.bits[2]) | (x.number.bits[1] & y.number.bits[1] & !ans.bits[2])
    carry && error("integer overflow or underflow")
    DistInt{W}(ans.bits[2:W+1])
end

function Base.:(-)(x::DistInt{W}, y::DistInt{W}) where W
    ans = DistUInt{W+1}(vcat([true], x.number.bits)) - DistUInt{W+1}(vcat([false], y.number.bits))
    borrow = (!x.number.bits[1] & y.number.bits[1] & ans.bits[2]) | (x.number.bits[1] & !y.number.bits[1] & !ans.bits[2])
    borrow && error("integer overflow or underflow")
    DistInt{W}(ans.bits[2:W+1])
end

function Base.:(*)(x::DistInt{W}, y::DistInt{W}) where W
    # ans = DistUInt{W+1}(vcat([true], x.number.bits)) - DistUInt{W+1}(vcat([false], y.number.bits))
    # borrow = (!x.number.bits[1] & y.number.bits[1] & ans.bits[2]) | (x.number.bits[1] & !y.number.bits[1] & !ans.bits[2])
    # borrow && error("integer overflow or underflow")
    # DistInt{W}(ans.bits[2:W+1])

    DistInt{W}(x.number * y.number)
end
  