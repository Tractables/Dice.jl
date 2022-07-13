
export DistInt, uniform

##################################
# types, structs, and constructors
##################################

struct DistInt{W} <: Dist{Int}
    # first index is least significant bit
    bits::Vector{AnyBool}
    function DistInt{W}(b) where W
        @assert length(b) == W
        @assert W <= 63
        new{W}(b)
    end
end

##################################
# inference
##################################

tobits(x::DistInt) = 
    filter(y -> y isa Dist{Bool}, x.bits)

function frombits(x::DistInt, world)
    v = 0
    for i = 1:bitwidth(x)
        if frombits(x.bits[i], world)
            v += 2^(i-1)
        end
    end
    v
end

##################################
# methods
##################################

function bitwidth(::DistInt{W}) where W 
    W
end

function uniform(::Type{DistInt{W}}) where W
    DistInt{W}([flip(0.5) for i=1:W])
end

##################################
# other method overloading
##################################

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
  