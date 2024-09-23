using Distributions
using SymPy

export DistFix, bitblast, bitblast_linear, bitblast_exponential, bitblast_exact, unit_exponential, exponential, laplace, unit_gamma, shift_point_gamma, n_unit_exponentials, geometric, general_gamma

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
        mantissa = drop_bits(DistInt{W1+(F2-F1)}, x.mantissa; last=false)
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
        iszero(linear_piece_probs[i]) && iszero(piece_probs[i]) && continue
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


function bitblast2(::Type{DistFix{W,F}}, dist::ContinuousUnivariateDistribution, 
                  numpieces::Int, start::Float64, stop::Float64, strategy=:linear) where {W,F}

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
        iszero(linear_piece_probs[i]) && iszero(piece_probs[i]) && continue
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

    @assert ispow2((stop - start)*2^F) "The number of $(1/2^F)-sized intervals between $start and $stop must be a power of two."
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

###################################################
# sound bit blasting for mixed gamma distributions
###################################################

# bit blasted exponential distribution on unit interval
# reverse=true refers to LSB to MSB order of flips 
function unit_exponential(t::Type{DistFix{W, F}}, beta::Float64; reverse=false) where W where F
    if !reverse
        DistFix{W, F}(vcat([false for i in 1:W-F], [flip(exp(beta/2^i)/(1+exp(beta/2^i))) for i in 1:F]))
    else
        DistFix{W, F}(vcat([false for i in 1:W-F], reverse([flip(exp(beta/2^i)/(1+exp(beta/2^i))) for i in F:-1:1])))
    end
end

# bit blasted exponential distribution on arbitrary interval
# reverse=true refers to LSB to MSB order of flips
# TODO: make the following function use unit_exponential
function exponential(t::Type{DistFix{W, F}}, beta::Float64, start::Float64, stop::Float64; reverse=false) where W where F   
    range = stop - start
    @assert ispow2(range)

    new_beta = beta*range
    bits = Int(log2(range)) + F
    
    if !reverse
        bit_vector = vcat([false for i in 1:W - bits], [flip(exp(new_beta/2^i)/(1+exp(new_beta/2^i))) for i in 1:bits])
    else 
        bit_vector = vcat([false for i in 1:W - bits], reverse([flip(exp(new_beta/2^i)/(1+exp(new_beta/2^i))) for i in bits:-1:1]))
    end
    DistFix{W, F}(bit_vector) + DistFix{W, F}(start)
end

function beta(d::ContinuousUnivariateDistribution, start::Float64, stop::Float64, interval_sz::Float64)
    prob_start = cdf(d, start + interval_sz) - cdf(d, start)
    if prob_start == 0.0
        prob_start = eps(0.0)
    end
    prob_end = cdf(d, stop) - cdf(d, stop - interval_sz)
    result = (log(prob_end) - log(prob_start)) / (stop - start - interval_sz)

    if result ≈ Inf
        @show prob_start
        @show prob_end
        @show start, stop, interval_sz
    end
    result
end

function bitblast_exponential(::Type{DistFix{W,F}}, dist::ContinuousUnivariateDistribution, 
    numpieces::Int, start::Float64, stop::Float64, strategy=:exponential) where {W,F}

    # basic checks
    @assert start >= -(2^(W - F - 1))
    @assert stop <= (2^(W - F - 1))
    @assert start < stop
    a = Int(log2((stop - start)*2^F))
    @assert a isa Int 
    @assert ispow2(numpieces) "Number of pieces must be a power of two"
    piece_bits = Int(log2(numpieces))
    if piece_bits == 0
        piece_bits = 1
    end
    @assert typeof(piece_bits) == Int

    # preliminaries
    d = truncated(dist, start, stop)
    whole_bits = a
    point = F
    interval_sz = (2^whole_bits/numpieces)
    bits = Int(log2(interval_sz))
    areas = Vector(undef, numpieces)
    total_area = 0

    beta_vec = Vector(undef, numpieces)
    start_pts = Vector(undef, numpieces)
    stop_pts = Vector(undef, numpieces)

    

    # Figuring out end points
    for i=1:numpieces
        p1 = start + (i-1)*interval_sz/2^point 
        p3 = start + (i)*interval_sz/2^point 

        beta_vec[i] = beta(d, p1, p3, 2.0^(-F))
        # if (beta_vec[i] in [Inf, -Inf]) | isnan(beta_vec[i])
        #     beta_vec[i] = 0.0
        # end

        areas[i] = (cdf.(d, p3) - cdf.(d, p1))
        # @show p1, p2, p3, p4, areas[i]
        start_pts[i] = p1
        stop_pts[i] = p3

        total_area += areas[i]
    end


    # @show beta_vec

    rel_prob = areas/total_area

    b = discrete(DistUInt{piece_bits}, rel_prob)

    ans = DistFix{W, F}((2^(W-1)-1)/2^F)

    for i=numpieces:-1:1
        ans = ifelse( prob_equals(b, DistUInt{piece_bits}(i-1)), 
                exponential(DistFix{W, F}, beta_vec[i], start_pts[i], stop_pts[i]),
                ans)  
    end
    return ans
end

function continuous(t::Type{DistFix{W, F}}, d::ContinuousUnivariateDistribution, pieces::Int, start::Float64, stop::Float64, exp::Bool=false) where {W, F}
    c = if exp
        continuous_exp(DistFix{W, F}, d, pieces, start, stop)
    else 
        continuous_linear(DistFix{W, F}, d, pieces, start, stop)
    end
    return c
end

# https://en.wikipedia.org/wiki/Laplace_distribution
function laplace(t::Type{DistFix{W, F}}, mean::Float64, scale::Float64, start::Float64, stop::Float64) where {W, F}
    @assert scale > 0

    beta1 = -1/scale
    e1 = exponential(DistFix{W, F}, beta1, mean, stop)

    beta2 = 1/scale
    e2 = exponential(DistFix{W, F}, beta2, start, mean)

    ifelse(flip(0.5), e1, e2)
end

#Helper function that returns exponentials 

function shift_point_gamma(::Type{DistFix{W, F}}, alpha::Int, beta::Float64) where {W, F}
    DFiP = DistFix{W, F}
    if alpha == 0
        unit_exponential(DFiP, beta)
    else
        x1 = shift_point_gamma(DFiP, alpha - 1, beta)
        x2 = uniform(DFiP, 0.0, 1.0)
        observe(ifelse(flip(1/(1 + 2.0^(-F))), x2 < x1, true))
        x1
    end
end

#https://www.wolframalpha.com/input?i=sum+%28a*epsilon%29%5E2+e%5E%28beta+*+epsilon+*+a%29+from+a%3D0+to+a%3D2%5Eb-1
function sum_qgp(β::Float64, ϵ::Float64)
    ans = (1/ϵ - 1)^2 * exp(β*ϵ*(2 + 1/ϵ))
    ans += (1/ϵ^2)*exp(β)
    ans += (2/ϵ - 2/ϵ^2 + 1)*exp(β * (1 + ϵ))
    ans -= exp(β*ϵ)
    ans -= exp(2*β*ϵ)
    ans *= ϵ^2
    ans /= (exp(β * ϵ) - 1)^3
    ans
end

#https://www.wolframalpha.com/input?i=sum+%28a*epsilon%29+*+e%5E%28beta+*+epsilon+*+a%29+from+a%3D0+to+a%3D2%5Eb-1
function sum_agp(β::Float64, ϵ::Float64)
    ans = (1/ϵ - 1)*exp(β*(1 + ϵ))
    ans -= exp(β)/ϵ
    ans += exp(β*ϵ)
    ans *= ϵ
    ans /= (exp(β*ϵ) - 1)^2
    ans
end

#https://www.wolframalpha.com/input?i=sum+e%5E%28beta+*+epsilon+*+a%29+from+a%3D0+to+a%3D2%5Eb-1
function sum_gp(β::Float64, ϵ::Float64)
    ans = (exp(β) - 1) / (exp(β*ϵ) - 1)
    ans
end

function sum_pgp(β::Float64, ϵ::Float64, p::Int)
    if p == 0
        sum_gp(β, ϵ)
    elseif p == 1
        sum_agp(β, ϵ)
    elseif p == 2
        sum_qgp(β, ϵ)
    else
        sum = 0
        for i = 0:ϵ:1-ϵ
            sum += i^p * exp(β*i)
        end
        sum
    end
end

function n_unit_exponentials(::Type{DistFix{W, F}}, betas::Vector{Float64}) where {W, F}
    DFiP = DistFix{W, F}
    l = length(betas)
    ans = Vector(undef, l)
    for i in 1:l
        ans[i] = Vector(undef, W)
    end
    for i in 1:W-F
        for j in 1:l
            ans[j][i] = false
        end
    end
    for i in F:-1:1
        for j in 1:l
            ans[j][i + W - F] = flip(exp(betas[j]/2^i)/(1+exp(betas[j]/2^i)))
        end
    end
    [DFiP(i) for i in ans] 
end

function exponential_for_gamma(α::Int, β::Float64)::Vector{Float64}
    if α == 0
        []
    elseif α == 1
        [β, β, 0.0]
    else
        v = []
        for i in 1:α
            v = vcat(vcat([β], zeros(i-1)), v)
        end

        vcat(vcat(exponential_for_gamma(α-1, β), [0.0]), v)
    end
end

function gamma_constants(α::Int, β::Float64, ϵ::Float64)
    @syms varint
    @syms v2
    if α == 0
        []
    else
        c1 = Float64(sympy.Poly(integrate(varint^α*exp(β*varint), (varint, 0, 1)), varint).coeffs().evalf()[1])
        c2 = [Float64(i) for i in sympy.Poly(simplify(v2*integrate(varint^(α-1)*exp(β*varint), (varint, v2, v2 + ϵ))/exp(β*v2)), v2).coeffs()]
        p1 = 0
        for i in eachindex(c2)
            p1 += sum_pgp(β, ϵ, length(c2) + 1 - i) * c2[i]
        end
        p1 /= c1

        c2 = [Float64(i) for i in sympy.Poly(simplify(v2*integrate(varint^(α-1) * (varint - v2) *exp(β*varint), (varint, v2, v2 + ϵ))/exp(β*v2)), v2).coeffs()]
        # @show c2
        # @show sympy.Poly(simplify(v2*integrate(varint^(α-1) * (varint - v2) *exp(β*varint), (varint, v2, v2 + ϵ))/exp(β*v2)), v2)
        p2 = Vector(undef, α)
        for i in eachindex(c2)
            p2[i] = sum_pgp(β, ϵ, length(c2) - i) * c2[i]
        end
        # @show p2
        
        vcat([p1], p2, gamma_constants(α-1, β, ϵ))
    end
end




function unit_gamma(t::Type{DistFix{W, F}}, alpha::Int, beta::Float64; vec_arg=[], constants = [], discrete_bdd=[], coinflips = []) where {W, F}
    DFiP = DistFix{W, F}
    if alpha == 0
        unit_exponential(DFiP, beta)
    elseif alpha == 1
        
        t = (exp(beta*2.0^(-F))*(beta*2.0^(-F) - 1) + 1)*(1 - exp(beta)) / ((1 - exp(beta*2.0^(-F)))*(exp(beta) * (beta - 1) + 1))
        
        if (length(coinflips) != 0)
            coinflip = coinflips[1]
        else
            coinflip = flip(t)
        end
        

        if (length(vec_arg) != 0)
            (Y, Z, U) = vec_arg
        else
            (Y, Z, U) = n_unit_exponentials(DFiP, [beta, beta, 0.0])
        end
        observe(U < Y)

        
        
        final = ifelse(coinflip, Z, Y)
        final
    else 
        α = alpha
        β = beta
        if (length(vec_arg) != 0)
            vec_expo = vec_arg
            
        else
            discrete_bdd = Vector(undef, α)
            constants = gamma_constants(alpha, beta, 1/2^F)

            t = (exp(beta*2.0^(-F))*(beta*2.0^(-F) - 1) + 1)*(1 - exp(beta)) / ((1 - exp(beta*2.0^(-F)))*(exp(beta) * (beta - 1) + 1))
            f = flip(t)

            count = 0
            for i in α:-1:1
                # @show constants
                l = discrete(DistUInt{max(Int(ceil(log(i))), 1)}, normalize(constants[count + 2:count+i+1]))
                count = count+i+1

                discrete_bdd[α - i + 1] = l
            end
            vec_expo = n_unit_exponentials(DFiP, exponential_for_gamma(α, β))
            
        end

        seq = Int(α*(α^2 + 5)/6)
        # @show constant_flips
        x1 = unit_gamma(DFiP, alpha-1, beta, vec_arg=vec_expo[1:seq], constants=constants[α + 2:length(constants)], discrete_bdd=discrete_bdd[2:α])
        x2 = vec_expo[seq + 1]
        observe(x2 < x1)

        discrete_dist_vec = Vector(undef, α)
        count = seq+2
        for i in 1:α 
            x = vec_expo[count]
            count+=1
            for j in 1:α - i
                observe(vec_expo[count] < x)
                count+=1
            end
            discrete_dist_vec[i] = x
        end

        # l = discrete(DistUInt{Int(ceil(log(α)))}, normalize(constants[2:α+1]))
        l = discrete_bdd[1]
        t = DFiP(0.0)
        for i in 1:α
            t = ifelse(prob_equals(l, DistUInt{Int(ceil(log(α)))}(i-1)), discrete_dist_vec[i], t)
        end
        
        ifelse(flip(constants[1]), x1, t)
    end

end

function normalize(v)
    l = sum(v)
    [i/l for i in v]    
end
# # TODO: Write tests for the following function
# function unit_concave(t::Type{DistFix{W, F}}, beta::Float64) where {W, F}
#     @assert beta <= 0
#     DFiP = DistFix{W, F}
#     Y = uniform(DFiP, 0.0, 1.0)
#     X = unit_exponential(DFiP, beta)
#     observe((X < Y)| prob_equals(X, Y))
#     Y
# end

######################################################################################################
# bit blasting geometric distribution: https://en.wikipedia.org/wiki/Geometric_distribution
######################################################################################################

# Creates a geometric distribution over the integers in the range [0, stop-1]
function geometric(::Type{DistFix{W, F}}, success::Float64, stop::Int) where {W, F}
    #TODO: use convert
    @assert ispow2(stop)
    bits = Int(log2(stop))
    @assert W - F > bits

    convert(DistFix{W, F}, DistFix{W, 0}(unit_exponential(DistFix{bits+1, bits}, log(1 - success)*2^bits).mantissa))
end

function general_gamma(::Type{DistFix{W, F}}, alpha::Int, beta::Float64, ll::Float64, ul::Float64) where {W, F}
    @assert ispow2(ul - ll)
    multiply = Int(log2(ul - ll))
    start = DistFix{W, F}(ul)
    new_type = DistFix{W, F + multiply} 

    DistFix{W, F}(unit_gamma(new_type, alpha, beta).mantissa.number.bits) + start
end
