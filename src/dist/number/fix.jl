using Distributions

export DistFix, bitblast

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

#################################
# bit blasting continuous distributions
#################################
  
function bitblast(::Type{DistFix{W,F}}, dist::ContinuousUnivariateDistribution, 
                  numpieces::Int, start::Float64, stop::Float64) where {W,F}

    # count bits and pieces
    @assert -(2^(W-F-1)) <= start < stop <= 2^(W-F-1)
    f_range_bits = log2((stop - start)*2^F)
    @assert isinteger(f_range_bits) "The number of $(2^F)-sized intervals between $start and $stop must be a power of two (not $f_range_bits)."
    @assert ispow2(numpieces) "Number of pieces must be a power of two (not $numpieces)"
    intervals_per_piece = (2^Int(f_range_bits))/numpieces
    bits_per_piece = Int(log2(intervals_per_piece))

    dist = truncated(dist, start, stop)

    total_prob = 0
    piece_probs = Vector(undef, numpieces) # prob of each piece
    end_probs = Vector(undef, numpieces) # prob of first and last interval in each piece
    linear_piece_probs = Vector(undef, numpieces) # prob of each piece if it were linear between end points

    for i=1:numpieces
        firstinter = start + (i-1)*intervals_per_piece/2^F 
        lastinter = start + (i)*intervals_per_piece/2^F 

        piece_probs[i] = (cdf.(dist, lastinter) - cdf.(dist, firstinter))
        total_prob += piece_probs[i]

        end_probs[i] = [cdf(dist, firstinter + 1/2^F ) - cdf(dist, firstinter), 
                        cdf(dist, lastinter) - cdf(dist, lastinter - 1/2^F )]
        linear_piece_probs[i] = (end_probs[i][1] + end_probs[i][2])/2 * 2^(bits_per_piece)
    end

    PieceChoice = DistUInt{max(1,Int(log2(numpieces)))}
    piecechoice = discrete(PieceChoice, piece_probs ./ total_prob) # selector variable for pieces
    piece_flips = Vector(undef, numpieces)
    l_vector = Vector(undef, numpieces)
    for i=numpieces:-1:1
        if (linear_piece_probs[i] == 0)
            a = 0.0
        else
            a = end_probs[i][1]/linear_piece_probs[i]
        end
        l_vector[i] = a > 1/2^bits_per_piece
        if l_vector[i]
            # @show 2 - a*2^bits, i, areas[i]
            piece_flips[i] = flip(2 - a*2^bits_per_piece)
        else
            # @show a*2^bits
            piece_flips[i] = flip(a*2^bits_per_piece)
        end  
    end

    unif = uniform(DistFix{W, F}, bits_per_piece)
    tria = triangle(DistFix{W, F}, bits_per_piece)
    ans = DistFix{W, F}((2^(W-1)-1)/2^F)

    for i=numpieces:-1:1
        ans = ifelse( prob_equals(piecechoice, PieceChoice(i-1)), 
                (if l_vector[i]
                    (ifelse(piece_flips[i], 
                        (DistFix{W, F}((i - 1)*2^bits_per_piece/2^F + start) + unif), 
                        (DistFix{W, F}((i*2^bits_per_piece - 1)/2^F + start) - tria)))
                else
                    (DistFix{W, F}((i - 1)*2^bits_per_piece/2^F + start) + 
                        ifelse(piece_flips[i], unif, tria))
                    
                end),
                ans)  
    end
    return ans
end
