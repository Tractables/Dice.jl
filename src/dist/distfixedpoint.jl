
export DistFixedPoint

##################################
# types, structs, and constructors
##################################

struct DistFixedPoint{W, F} <: Dist{Int}
    number::DistSignedInt{W}
    function DistFixedPoint{W, F}(b) where W where F
        @assert W >= F
        new{W, F}(b)
    end

end

function DistFixedPoint{W, F}(b::Vector) where W where F
    DistFixedPoint{W, F}(DistSignedInt{W}(b))
end

function DistFixedPoint{W, F}(i::Float64) where W where F
    new_i = Int(round(if i >= 0 i*2^F else i*2^F + 2^W end))
    DistFixedPoint{W, F}(DistSignedInt{W}(new_i))
end

# ##################################
# # inference
# ##################################

tobits(x::DistFixedPoint) = tobits(x.number)

function frombits(x::DistFixedPoint{W, F}, world) where W where F
    frombits(x.number, world)/2^F
end

# ##################################
# # expectation
# ##################################

function expectation(x::DistFixedPoint{W, F}) where W where F
    expectation(x.number)/2^F
end
    

# ##################################
# # methods
# ##################################

bitwidth(::DistFixedPoint{W, F}) where W where F = W

function uniform(::Type{DistFixedPoint{W, F}}, n = W) where W where F
    DistFixedPoint{W, F}(DistSignedInt{W}(uniform(DistInt{W}, n).bits))
end

function triangle(t::Type{DistFixedPoint{W, F}}, b::Int) where W where F
    @assert b < W
    DistFixedPoint{W, F}(triangle(DistSignedInt{W}, b))
end

##################################
# other method overloading
##################################

function prob_equals(x::DistFixedPoint{W, F}, y::DistFixedPoint{W, F}) where W where F
    prob_equals(x.number, y.number)
end

function ifelse(cond::Dist{Bool}, then::DistFixedPoint{W, F}, elze::DistFixedPoint{W, F}) where W where F
    DistFixedPoint{W, F}(ifelse(cond, then.number, elze.number))
end
  