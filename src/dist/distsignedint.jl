
export DistSignedInt

##################################
# types, structs, and constructors
##################################

struct DistSignedInt{W} <: Dist{Int}
    number::DistInt{W}
end

function DistSignedInt{W}(b::Vector) where W
    DistSignedInt{W}(DistInt{W}(b))
end

function DistSignedInt{W}(i::Int) where W
    new_i = if i >= 0 i else i + 2^W end
    DistSignedInt{W}(DistInt{W}(new_i))
end

##################################
# inference
##################################

tobits(x::DistSignedInt) = 
    filter(y -> y isa Dist{Bool}, x.number.bits)

function frombits(x::DistSignedInt{W}, world) where W
    v = 0
    if frombits(x.number.bits[1], world)
        v += -2^(W-1)
    end
    for i = 2:W
        if frombits(x.number.bits[i], world)
            v += 2^(W-i)
        end
    end
    v
end

##################################
# expectation
##################################

function expectation(x::DistSignedInt{W}) where W
    ans = 0
    a = pr(x.number.bits...)
    start = 2^(W-1)
    ans -= start*a[1][1]
    start /= 2
    for i=2:W
        ans += start*a[i][1]
        start /= 2
    end
    ans
end
    

##################################
# methods
##################################

bitwidth(::DistSignedInt{W}) where W = W

function uniform(::Type{DistSignedInt{W}}, n = W) where W
    DistSignedInt{W}(uniform(DistInt{W}, n).bits)
end

##################################
# casting
##################################

function Base.convert(x::DistSignedInt{W1}, t::Type{DistSignedInt{W2}}) where W1 where W2
    if W1 <= W2
        DistSignedInt{W2}(vcat(fill(x.number.bits[1], W2 - W1), x.number.bits))
    else
        #TODO: throw error if msb is not irrelevant
        DistSignedInt{W2}(x.number.bits[W1 - W2 + 1:W1])
    end
end


# ##################################
# # other method overloading
# ##################################

function prob_equals(x::DistSignedInt{W}, y::DistSignedInt{W}) where W
    prob_equals(x.number, y.number)
end

function Base.ifelse(cond::Dist{Bool}, then::DistSignedInt{W}, elze::DistSignedInt{W}) where W
    DistSignedInt{W}(ifelse(cond, then.number, elze.number))
end
  