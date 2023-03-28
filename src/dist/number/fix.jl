using Distributions

export DistFix, continuous

##################################
# types, structs, and constructors
##################################

"A signed fixed point number with `W` bits of which `F` are after the binary point"
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
    mantissa = DistInt{W}(floor(Int, x*2^F))
    DistFix{W, F}(mantissa)
end

function uniform(::Type{DistFix{W, F}}, n = W) where {W,F}
    DistFix{W, F}(uniform(DistInt{W}, n))
end

function uniform(t::Type{DistFix{W, F}}, start, stop; rtol=√eps(), kwargs...) where {W,F}
    @assert -(2^(W-F-1)) <= start < stop <= 2^(W-F-1)
    start = start > 0 ? start*(1+rtol) : start*(1-rtol)
    stop =  stop  > 0 ? stop*(1-rtol)  : stop*(1+rtol) 
    startint = floor(Int, start*2^F)
    stopint = ceil(Int, (stop*2^F))
    mantissa = uniform(DistInt{W}, startint, stopint; kwargs...)
    DistFix{W, F}(mantissa)
 end
 

function triangle(t::Type{DistFix{W, F}}, b::Int) where {W,F}
    DistFix{W, F}(triangle(DistInt{W}, b))
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
    frombits(x.mantissa, world)/2^F
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

bitwidth(::DistFix{W, F}) where {W,F} = W

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
    x1 = convert(DistFix{W+F, F}, x)
    y1 = convert(DistFix{W+F, F}, y)
    prodint = x1.mantissa * y1.mantissa
    prodfip = DistFix{W+F, 2F}(prodint)
    convert(DistFix{W, F}, prodfip)
end

function Base.:(/)(x::DistFix{W, F}, y::DistFix{W, F}) where {W, F}
    xp = convert(DistFix{W+F, 2*F}, x)
    yp = convert(DistFix{W+F, F}, y)
    ans = xp.mantissa / yp.mantissa

    n_overflow = DistInt{F+1}(ans.number.bits[1:F+1])
    overflow = !prob_equals(n_overflow, DistInt{F+1}(-1)) & !iszero(n_overflow)
    errorcheck() & overflow && error("integer overflow")

    DistFix{W, F}(ans.number.bits[F+1:W+F])
end

#################################
# continuous distributions
#################################
  
function continuous(t::Type{DistFix{W, F}}, d::ContinuousUnivariateDistribution, pieces::Int, start::Float64, stop::Float64) where {W, F}

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

    unif = uniform(DistFix{W, F}, bits)
    tria = triangle(DistFix{W, F}, bits)
    ans = DistFix{W, F}((2^(W-1)-1)/2^F)

    for i=pieces:-1:1
        ans = ifelse( prob_equals(b, DistUInt{piece_bits}(i-1)), 
                (if l_vector[i]
                    (ifelse(piece_flips[i], 
                        (DistFix{W, F}((i - 1)*2^bits/2^F + start) + unif), 
                        (DistFix{W, F}((i*2^bits - 1)/2^F + start) - tria)))
                else
                    (DistFix{W, F}((i - 1)*2^bits/2^F + start) + 
                        ifelse(piece_flips[i], unif, tria))
                    
                end),
                ans)  
    end
    return ans
end
