using Distributions

export DistFix, bitblast, bitblast_linear, bitblast_exact

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
    @assert isinteger(f_range_bits) "The number of $(1/2^F)-sized intervals between $start and $stop must be a power of two (not $f_range_bits)."
    @assert ispow2(numpieces) "Number of pieces must be a power of two (not $numpieces)"
    intervals_per_piece = (2^Int(f_range_bits))/numpieces
    bits_per_piece = Int(log2(intervals_per_piece))

    dist = truncated(dist, start, stop)

    total_prob = 0
    piece_probs = Vector(undef, numpieces) # prob of each piece
    border_probs = Vector(undef, numpieces) # prob of first and last interval in each piece
    linear_piece_probs = Vector(undef, numpieces) # prob of each piece if it were linear between end points

    for i=1:numpieces
        firstinter = start + (i-1)*intervals_per_piece/2^F 
        lastinter = start + (i)*intervals_per_piece/2^F 

        piece_probs[i] = (cdf(dist, lastinter) - cdf(dist, firstinter))
        total_prob += piece_probs[i]

        border_probs[i] = [cdf(dist, firstinter + 1/2^F ) - cdf(dist, firstinter), 
                        cdf(dist, lastinter) - cdf(dist, lastinter - 1/2^F )]
        linear_piece_probs[i] = (border_probs[i][1] + border_probs[i][2])/2 * 2^(bits_per_piece)
    end

    PieceChoice = DistUInt{max(1,Int(log2(numpieces)))}
    piecechoice = discrete(PieceChoice, piece_probs ./ total_prob) # selector variable for pieces
    slope_flips = Vector(undef, numpieces)

    isdecreasing = Vector(undef, numpieces)
    for i=numpieces:-1:1
        iszero(linear_piece_probs[i]) && assert(iszero(piece_probs[i])) && continue
        a = border_probs[i][1]/linear_piece_probs[i]
        isdecreasing[i] = a > 1/2^bits_per_piece
        if isdecreasing[i]
            slope_flips[i] = flip(2-a*2^bits_per_piece)
        else
            slope_flips[i] = flip(a*2^bits_per_piece)
        end  
    end

    unif = uniform(DistFix{W,F},  bits_per_piece)
    tria = triangle(DistFix{W,F}, bits_per_piece)
    z = nothing
    for i=1:numpieces
        iszero(linear_piece_probs[i]) && continue
        firstinterval = DistFix{W,F}(start + (i-1)*2^bits_per_piece/2^F)
        lastinterval = DistFix{W,F}(start + (i*2^bits_per_piece-1)/2^F)
        linear_dist = 
            if isdecreasing[i]
                (ifelse(slope_flips[i], 
                    (firstinterval + unif), 
                    (lastinterval - tria)))
            else
                firstinterval + ifelse(slope_flips[i], unif, tria)
            end
        z = if isnothing(z)
                linear_dist
            else
                ifelse(prob_equals(piecechoice, PieceChoice(i-1)), linear_dist, z)  
            end
    end
    return z
end


function bitblast(::Type{DistFix{W,F}}, dist::ContinuousUnivariateDistribution, 
                  start::Float64, stop::Float64, blast_strategy=:exact; kwargs...) where {W,F}
    if blast_strategy == :linear
        bitblast_linear(DistFix{W,F}, dist, start, stop; kwargs...)
    else
        error("Unknown bitblasting strategy: $strategy")
    end
end

"Approximate a continuous distribution on an interval using a bit-blasted linear density"
function bitblast_linear(::Type{DistFix{W,F}}, dist::ContinuousUnivariateDistribution, 
                  start::Float64, stop::Float64;
                  slope_flip = nothing, unif = nothing, tria = nothing) where {W,F}

    dist = truncated(dist, start, stop)
    firstprob = cdf(dist, start + 1/2^F ) - cdf(dist, start)
    lastprob = cdf(dist, stop) - cdf(dist, stop - 1/2^F)
    avgprob = (firstprob + lastprob)/2

    @assert !iszero(firstprob) || !iszero(lastprob) "No probability mass found at the given boundaries."

    @assert isinteger(log2((stop - start)*2^F)) "The number of $(1/2^F)-sized intervals between $start and $stop must be a power of two."
    num_bits = Int(log2((stop-start)*2^F))
    isnothing(slope_flip) && (slope_flip = flip())
    isnothing(unif) && (unif = uniform(DistFix{W,F}, num_bits))
    isnothing(tria) && (tria = triangle(DistFix{W,F}, num_bits))

    firstinterval = DistFix{W,F}(start)
    lastinterval = DistFix{W,F}(start + (2^num_bits-1)/2^F)
    if firstprob > avgprob # the slope is decreasing
        slope_flip = flip_prob!(slope_flip, 2-firstprob/avgprob)
        ifelse(slope_flip, (firstinterval + unif), (lastinterval - tria))
    else # the slope is increasing
        slope_flip = flip_prob!(slope_flip, firstprob/avgprob)
        firstinterval + ifelse(slope_flip, unif, tria)
    end  
end