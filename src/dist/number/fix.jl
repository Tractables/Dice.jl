using Distributions

export DistFix

##################################
# types, structs, and constructors
##################################

"A signed fixed point number with `W` bits in mantissa and exponent as 2^{-F}"
struct DistFix{W, F} <: Dist{Int}
    mantissa::DistInt{W}
    function DistFix{W, F}(b) where {W,F}
        @assert F <= W
        new{W, F}(b)
    end
end

function DistFix{W, F}(b::AbstractVector) where {W,F}
    DistFix{W, F}(DistInt{W}(b))
end

function DistFix{W, F}(x::Float64) where {W,F}
    mantissa = DistInt{W}(floor(Int, x*2^float(F)))
    DistFix{W, F}(mantissa)
end

function uniform(::Type{DistFix{W, F}}, n = W) where {W,F}
    DistFix{W, F}(uniform(DistInt{W}, n))
end

function Base.convert(::Type{DistFix{W2, F2}}, x::DistFix{W1, F1}) where {W1,W2,F1,F2}
    if (F1 == F2)
        return DistFix{W2, F2}(convert(DistInt{W2}, x.mantissa))
    elseif (F2 > F1)
        mantissa = convert(DistInt{W1+(F2-F1)}, x.mantissa)
        mantissa <<= (F2-F1)
    else #F2 < F1
        mantissa = drop_bits(DistInt{W1+(F2-F1)}, x.mantissa; last=true)
    end
    convert(DistFix{W2, F2}, DistFix{W1+(F2-F1), F2}(mantissa))
end

# ##################################
# # inference
# ##################################

tobits(x::DistFix) = tobits(x.mantissa)

function frombits(x::DistFix{W, F}, world) where {W,F}
    frombits(x.mantissa, world)/2^float(F)
end

function expectation(x::DistFix{W, F}; kwargs...) where {W,F}
    expectation(x.mantissa; kwargs...)/2^F
end

function variance(x::DistFix{W, F}; kwargs...) where {W,F}
    variance(x.mantissa; kwargs...)/2^(2*F)
end
    
# ##################################
# # methods
# ##################################

bitwidth(::DistFix{W}) where W = W

function prob_equals(x::DistFix{W, F}, y::DistFix{W, F}) where {W,F}
    prob_equals(x.mantissa, y.mantissa)
end

function Base.isless(x::DistFix{W, F}, y::DistFix{W, F}) where {W,F}
    isless(x.mantissa, y.mantissa)
end

function Base.ifelse(cond::Dist{Bool}, then::DistFix{W, F}, elze::DistFix{W, F}) where {W,F}
    DistFix{W, F}(ifelse(cond, then.mantissa, elze.mantissa))
end

function Base.:(+)(x::DistFix{W, F}, y::DistFix{W, F}) where {W, F}
    DistFix{W, F}(x.mantissa + y.mantissa)
end

function Base.:(-)(x::DistFix{W, F}, y::DistFix{W, F}) where {W, F}
    DistFix{W, F}(x.mantissa - y.mantissa)
end

function Base.:(*)(x::DistFix{W, F}, y::DistFix{W, F}) where {W, F}
    xbig = convert(DistFix{W+F,F}, x)
    ybig = convert(DistFix{W+F,F}, y)
    z_mantissa = xbig.mantissa * ybig.mantissa
    zbig = DistFix{W+F,2F}(z_mantissa)
    convert(DistFix{W,F}, zbig)
end

function Base.:(/)(x::DistFix{W, F}, y::DistFix{W, F}) where {W, F}
    xbig = convert(DistFix{W+F,2F}, x)
    ybig = convert(DistFix{W+F,F}, y)
    z_mantissa_big = xbig.mantissa / ybig.mantissa
    z_mantissa = convert(DistInt{W}, z_mantissa_big)
    DistFix{W, F}(z_mantissa)
end
