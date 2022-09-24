using Distributions

export DistFixedPoint, continuous

##################################
# types, structs, and constructors
##################################

struct DistFixedPoint{W, F} <: Dist{Int}
    # W: total number of bits, F: number of bits after the binary point
    number::DistInt{W}
    function DistFixedPoint{W, F}(b) where W where F
        @assert W >= F
        new{W, F}(b)
    end

end

function DistFixedPoint{W, F}(b::Vector) where W where F
    DistFixedPoint{W, F}(DistInt{W}(b))
end

function DistFixedPoint{W, F}(i::Float64) where W where F
    # new_i = Int(round(if i >= -(2.0)^(-F-1) i*2^F else i*2^F + 2^W end)) # for a centered notation of probabilities
    new_i = Int(floor(if i >= 0 i*2^F else i*2^F + 2^W end))
    # @show new_i
    DistFixedPoint{W, F}(DistInt{W}(DistUInt{W}(new_i)))
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

function expectation(x::DistFixedPoint{W, F}; kwargs...) where W where F
    expectation(x.number; kwargs...)/2^F
end
    

# ##################################
# # methods
# ##################################

bitwidth(::DistFixedPoint{W, F}) where W where F = W

function uniform(::Type{DistFixedPoint{W, F}}, n = W) where W where F
    DistFixedPoint{W, F}(DistInt{W}(uniform(DistUInt{W}, n).bits))
end

function uniform(t::Type{DistFixedPoint{W, F}}, start::Float64, stop::Float64) where W where F
    @assert start >= -(2^(W - F - 1))
    @assert stop <= (2^(W - F - 1))
    @assert start < stop
    a = Int(round((stop - start)*2^F))
    return DistFixedPoint{W, F}(uniform(DistInt{W}, 0, a)) + DistFixedPoint{W, F}(start)
 end
 

function triangle(t::Type{DistFixedPoint{W, F}}, b::Int) where W where F
    @assert b <= W
    DistFixedPoint{W, F}(triangle(DistInt{W}, b))
end

##################################
# casting
##################################

function Base.convert(x::DistFixedPoint{W1, F1}, t::Type{DistFixedPoint{W2, F2}}) where W1 where W2 where F1 where F2
    #TODO: check if cases are exhaustive
    if (F1 == F2)
        DistFixedPoint{W2, F2}(convert(x.number, DistInt{W2}))
    elseif (W1 - F1 == W2 - F2)
        if (F2 > F1)
            DistFixedPoint{W2, F2}(vcat(x.number.number.bits, fill(false, F2 - F1)))
        else
            DistFixedPoint{W2, F2}(x.number.number.bits[1:W2])
        end
    end
end

##################################
# other method overloading
##################################

function prob_equals(x::DistFixedPoint{W, F}, y::DistFixedPoint{W, F}) where W where F
    prob_equals(x.number, y.number)
end

function Base.ifelse(cond::Dist{Bool}, then::DistFixedPoint{W, F}, elze::DistFixedPoint{W, F}) where W where F
    DistFixedPoint{W, F}(ifelse(cond, then.number, elze.number))
end

function Base.:(+)(x::DistFixedPoint{W, F}, y::DistFixedPoint{W, F}) where {W, F}
    DistFixedPoint{W, F}(x.number + y.number)
end

function Base.:(-)(x::DistFixedPoint{W, F}, y::DistFixedPoint{W, F}) where {W, F}
    DistFixedPoint{W, F}(x.number - y.number)
end

function Base.:(*)(x::DistFixedPoint{W, F}, y::DistFixedPoint{W, F}) where {W, F}
    x1 = convert(x, DistFixedPoint{W+F, F})
    y1 = convert(y, DistFixedPoint{W+F, F})
    prodint = x1.number * y1.number
    prodfip = DistFixedPoint{W+F, 2F}(prodint)
    convert(prodfip, DistFixedPoint{W, F})
end

#################################
# continuous distributions
#################################
  
function continuous(t::Type{DistFixedPoint{W, F}}, d::ContinuousUnivariateDistribution, pieces::Int, start::Float64, stop::Float64) where {W, F}

    # basic checks
    @assert start >= -(2^(W - F - 1))
    @assert stop <= (2^(W - F - 1))
    @assert start < stop
    a = Int(log2((stop - start)*2^F))
    @assert a isa Int 
    @assert ispow2(pieces) "Number of pieces must be a power of two"
    piece_bits = Int(log2(pieces))
    if piece_bits == 0
        piece_bits = 1
    end
    @assert typeof(piece_bits) == Int

    # preliminaries
    d = truncated(d, start, stop)
    whole_bits = a
    point = F
    interval_sz = (2^whole_bits/pieces)
    bits = Int(log2(interval_sz))
    areas = Vector(undef, pieces)
    trap_areas = Vector(undef, pieces)
    total_area = 0
    end_pts = Vector(undef, pieces)

    # Figuring out end points
    for i=1:pieces
        p1 = start + (i-1)*interval_sz/2^point 
        p2 = p1 + 1/2^(point) 
        p3 = start + (i)*interval_sz/2^point 
        p4 = p3 - 1/2^point 

        # @show p1, p2, p3, p4

        pts = [cdf.(d, p2) - cdf.(d, p1), cdf.(d, p3) - cdf.(d, p4)]
        end_pts[i] = pts

        trap_areas[i] = (pts[1] + pts[2])*2^(bits - 1)
        areas[i] = (cdf.(d, p3) - cdf.(d, p1))
        # @show p1, p2, p3, p4, areas[i]

        total_area += areas[i]
    end

    rel_prob = areas/total_area

    # @show rel_prob
    # @show areas

    b = discrete(DistUInt{piece_bits}, rel_prob)
    
    #Move flips here
    piece_flips = Vector(undef, pieces)
    l_vector = Vector(undef, pieces)
    for i=pieces:-1:1
        if (trap_areas[i] == 0)
            a = 0.0
        else
            a = end_pts[i][1]/trap_areas[i]
        end
        l_vector[i] = a > 1/2^bits
        if l_vector[i]
            # @show 2 - a*2^bits, i, areas[i]
            piece_flips[i] = flip(2 - a*2^bits)
        else
            # @show a*2^bits
            piece_flips[i] = flip(a*2^bits)
        end  
    end

    unif = uniform(DistFixedPoint{W, F}, bits)
    tria = triangle(DistFixedPoint{W, F}, bits)
    ans = DistFixedPoint{W, F}((2^(W-1)-1)/2^F)

    for i=pieces:-1:1
        ans = ifelse( prob_equals(b, DistUInt{piece_bits}(i-1)), 
                (if l_vector[i]
                    (ifelse(piece_flips[i], 
                        (DistFixedPoint{W, F}((i - 1)*2^bits/2^F + start) + unif), 
                        (DistFixedPoint{W, F}((i*2^bits - 1)/2^F + start) - tria)))
                else
                    (DistFixedPoint{W, F}((i - 1)*2^bits/2^F + start) + 
                        ifelse(piece_flips[i], unif, tria))
                    
                end),
                ans)  
    end
    return ans
end
