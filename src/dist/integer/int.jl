
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
    new_i = ifelse(i >= 0, i, i + 2^W)
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

function variance(x::DistInt{W}; kwargs...) where W
    queries = Vector(undef, Int((W * (W-1))/2))
    counter = 1
    for i = 1:W-1
        for j = i+1:W
            queries[counter] = x.number.bits[i] & x.number.bits[j]
            counter += 1
        end
    end

    prs = pr(x.number.bits..., queries... ; kwargs...)


    # ans = 0
    # mb = T
    # b1 = t1.number
    probs = Matrix(undef, W, W)
    counter = 1
    for i = 1:W-1
        for j = i+1:W
            probs[i, j] = prs[counter + W][1.0]
            probs[j, i] = prs[counter + W][1.0]
            counter += 1
        end
        probs[i, i] = prs[i][1.0]
    end
    probs[W, W] = prs[W][1.0]
    ans = 0
    
    exponent1 = 1
    for i = 1:W
        ans += exponent1*(probs[W+1 - i, W+1 - i] - probs[W + 1 - i, W + 1 - i]^2)
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
                # ans -= 2*exponent2 * (probs[i, mb] - probs[i, i] * probs[mb, mb])
            end
        end
        # @show exponent2 exponent1
        
        exponent1 = exponent1*4
    end
    return ans
end

##################################
# methods
##################################

bitwidth(::DistInt{W}) where W = W

function uniform(::Type{DistInt{W}}, n = W) where W
    DistInt{W}(uniform(DistUInt{W}, n).bits)
end

function uniform(::Type{DistInt{W}}, start::Int, stop::Int; ite::Bool=false) where W
    @assert start >= -(2^(W - 1))
    @assert stop <= (2^(W - 1))
    @assert start < stop
    ans = DistInt{W+1}(uniform(DistUInt{W+1}, 0, stop - start; ite=ite)) + DistInt{W+1}(start)
    return convert(ans, DistInt{W})
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

function Base.isless(x::DistInt{W}, y::DistInt{W}) where W
    ifelse(x.number.bits[1] & !y.number.bits[1], 
        true, 
    ifelse(!x.number.bits[1] & y.number.bits[1], 
            false, 
            isless(DistUInt{W-1}(x.number.bits[2:W]), DistUInt{W-1}(y.number.bits[2:W])))
    )
end

function Base.ifelse(cond::Dist{Bool}, then::DistInt{W}, elze::DistInt{W}) where W
    DistInt{W}(ifelse(cond, then.number, elze.number))
end

function Base.:(+)(x::DistInt{W}, y::DistInt{W}) where W
    ans = convert(x.number, DistUInt{W+1}) + convert(y.number, DistUInt{W+1})
    # a sufficient condition for avoiding overflow is that the first two bits are all the same in both operands
    cannot_overflow = prob_equals(y.number.bits[1], y.number.bits[2]) & prob_equals(x.number.bits[1], x.number.bits[2])
    # this sufficient condition is more easily proven true than the exact one, test it first
    overflow = !cannot_overflow & ((!x.number.bits[1] & !y.number.bits[1] & ans.bits[2]) | (x.number.bits[1] & y.number.bits[1] & !ans.bits[2]))
    overflow && error("integer overflow or underflow")
    DistInt{W}(ans.bits[2:W+1])
end

function Base.:(-)(x::DistInt{W}, y::DistInt{W}) where W
    ans = DistUInt{W+1}(vcat([true], x.number.bits)) - DistUInt{W+1}(vcat([false], y.number.bits))
    borrow = (!x.number.bits[1] & y.number.bits[1] & ans.bits[2]) | (x.number.bits[1] & !y.number.bits[1] & !ans.bits[2])
    borrow && error("integer overflow or underflow")
    DistInt{W}(ans.bits[2:W+1])
end

function Base.:(*)(x::DistInt{W}, y::DistInt{W}) where W
    p1 = convert(x, DistInt{2*W}).number
    p2 = convert(y, DistInt{2*W}).number
    P = DistUInt{2*W}(0)
    shifted_bits = p1.bits
    for i = 2*W:-1:1
        if (i != 2*W)
            shifted_bits = vcat(shifted_bits[2:2*W], false)
        end
        added = ifelse(p2.bits[i], DistUInt{2*W}(shifted_bits), DistUInt{2*W}(0))
        P = convert(P, DistUInt{2*W+2}) + convert(added, DistUInt{2*W+2})
        P = convert(P, DistUInt{2*W})
    end
    P_ans = convert(DistInt{2*W}(P), DistInt{W})
    P_overflow = DistInt{W}(P.bits[1:W])
    overflow = (!prob_equals(P_overflow, DistInt{W}(-1)) & !prob_equals(P_ans, DistInt{W}(-1))) | (!prob_equals(P_overflow, DistInt{W}(0)) & !prob_equals(P_ans, DistInt{W}(0)))
    overflow = prob_equals(P_overflow, DistInt{W}(-1)) | prob_equals(P_overflow, DistInt{W}(0))
    !overflow && error("integer overflow")
    overflow = !prob_equals(x, DistInt{W}(0)) & !prob_equals(y, DistInt{W}(0)) & ((!xor(p1.bits[W+1], p2.bits[W+1]) & P.bits[W+1]) | (xor(p1.bits[W+1], p2.bits[W+1]) & !P.bits[W+1]))
    overflow && error("integer overflow")
    return P_ans
end

function Base.:(/)(x::DistInt{W}, y::DistInt{W}) where W
    overflow = prob_equals(x, DistInt{W}(-2^(W-1))) & prob_equals(y, DistInt{W}(-1))
    overflow && error("integer overflow")

    is_zero = prob_equals(y, DistInt{W}(0))
    is_zero && error("division by zero")

    xp = if x.number.bits[1] DistUInt{W}(1) + DistUInt{W}([!xb for xb in x.number.bits]) else x.number end
    xp = convert(xp, DistUInt{W+1})
    yp = if y.number.bits[1] DistUInt{W}(1) + DistUInt{W}([!yb for yb in y.number.bits]) else y.number end
    yp = convert(yp, DistUInt{W+1})
    ans = xp / yp

    isneg = xor(x.number.bits[1], y.number.bits[1]) & !prob_equals(ans, DistUInt{W+1}(0))

    ans = if isneg DistUInt{W+1}(1) + DistUInt{W+1}([!ansb for ansb in ans.bits]) else ans end
    ans = DistInt{W}(ans.bits[2:W+1])
    return ans
end

function Base.:(%)(x::DistInt{W}, y::DistInt{W}) where W
    # overflow = prob_equals(x, DistInt{W}(-2^(W-1))) & prob_equals(y, DistInt{W}(-1))
    # overflow && error("integer overflow")

    is_zero = prob_equals(y, DistInt{W}(0))
    is_zero && error("division by zero")

    xp = if x.number.bits[1] DistUInt{W}(1) + DistUInt{W}([!xb for xb in x.number.bits]) else x.number end
    xp = convert(xp, DistUInt{W+1})
    yp = if y.number.bits[1] DistUInt{W}(1) + DistUInt{W}([!yb for yb in y.number.bits]) else y.number end
    yp = convert(yp, DistUInt{W+1})
    ans = xp % yp

    isneg = x.number.bits[1] & !prob_equals(ans, DistUInt{W+1}(0))

    ans = if isneg DistUInt{W+1}(1) + DistUInt{W+1}([!ansb for ansb in ans.bits]) else ans end
    ans = DistInt{W}(ans.bits[2:W+1])
    return ans
end
