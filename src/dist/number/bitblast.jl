using Distributions
using SymPy

export bitblast, bitblast_linear, bitblast_sample, bitblast_exponential, bitblast_exact, unit_exponential, exponential, laplace, unit_gamma, shift_point_gamma, n_unit_exponentials, geometric, general_gamma

#################################
# primitives for distributions
#################################

"""
    uniform(::Type{DistFix{W, F}}, start, stop; rtol=√eps(), kwargs...)

Returns a uniform distribution of type `DistFix{W, F}` in the range [start, stop)
"""
function uniform(::Type{DistFix{W, F}}, start, stop; rtol=√eps(), kwargs...) where {W,F}
    @assert -(2^(W-F-1)) <= start < stop <= 2^(W-F-1)
    start = start > 0 ? start*(1+rtol) : start*(1-rtol)
    stop =  stop  > 0 ? stop*(1-rtol)  : stop*(1+rtol) 
    startint = floor(Int, start*2^float(F))
    stopint = ceil(Int, (stop*2^float(F)))
    mantissa = uniform(DistInt{W}, startint, stopint; kwargs...)
    DistFix{W, F}(mantissa)
 end
 
"""
    triangle(::Type{DistFix{W, F}}, b::Int)

Returns a triangle distribution with a range of `b` bits. A triangle distribution over `b` bits refers to the distributions that assigns probability 0 to 0 and increases linearly with probability 2/(2^b)*(2^b - 1)
"""
function triangle(::Type{DistFix{W, F}}, b::Int) where {W,F}
    DistFix{W, F}(triangle(DistInt{W}, b))
end

"""
    unit_exponential(::Type{DistFix{W, F}}, beta::Float64; reverse=false)

Returns an exponential distribution e^(beta*x) in the range [0, 1) of the specified type.
For advanced users: `reverse` is used to control the order in which flips are created. `reverse=false` refers to the order of flips from MSB to LSB. 
"""
function unit_exponential(::Type{DistFix{W, F}}, beta::Float64; reverse=false) where W where F
    if !reverse
        DistFix{W, F}(vcat([false for i in 1:W-F], [flip(exp(beta/2^i)/(1+exp(beta/2^i))) for i in 1:F]))
    else
        DistFix{W, F}(vcat([false for i in 1:W-F], [flip(exp(beta/2^i)/(1+exp(beta/2^i))) for i in F:-1:1][F:-1:1]))
    end
end

"""
    exponential(::Type{DistFix{W, F}}, beta::Float64, start::Float64, stop::Float64; reverse=false)

Returns an exponential distribution e^(beta*x) in the range [start, stop) of the specified type.
"""
function exponential(::Type{DistFix{W, F}}, beta::Float64, start::Float64, stop::Float64; reverse=false) where W where F   
    range = stop - start
    # TODO: Implement exponential for any arbitrary range
    @assert ispow2(range) "Currently the function 'exponential' only supports range that is a power of 2."
    
    new_beta = beta*range
    bits = Int(log2(range)) + F

    intermediate = unit_exponential(DistFix{bits+1, bits}, new_beta; reverse = reverse)
    bit_vector = vcat([false for i in 1:W-bits], intermediate.mantissa.number.bits[2:bits+1]...)
    DistFix{W, F}(bit_vector) + DistFix{W, F}(start)
end

"""
    laplace(::Type{DistFix{W, F}}, mean::Float64, scale::Float64, start::Float64, stop::Float64)

Returns a Laplace distribution with the given mean and scale in the specified range [start, stop) of the specified type.
For more information: https://en.wikipedia.org/wiki/Laplace_distribution
"""
function laplace(::Type{DistFix{W, F}}, mean::Float64, scale::Float64, start::Float64, stop::Float64) where {W, F}
    @assert scale > 0
    
    coinflip = flip(0.5)
  
    beta1 = -1/scale
    e1 = exponential(DistFix{W, F}, beta1, mean, stop)
    
    beta2 = 1/scale
    e2 = exponential(DistFix{W, F}, beta2, start, mean)
    
    ifelse(coinflip, e1, e2)
end

"""
    n_unit_exponentials(::Type{DistFix{W, F}}, betas::Vector{Float64})

Returns n exponential distributions over the unit range with interleaved bits for a smaller BDD size.
"""
function n_unit_exponentials(::Type{DistFix{W, F}}, betas::Vector{Float64}) where {W, F}
    DFiP = DistFix{W, F}
    l = length(betas)
    ans = [vcat([false for _ in 1:W-F], Vector(undef, F)) for _ in 1:l]
    
    for i in F:-1:1
        for j in 1:l
            ans[j][i + W - F] = flip(exp(betas[j]/2^i)/(1+exp(betas[j]/2^i)))
        end
    end

    [DFiP(i) for i in ans] 
end


"""
    geometric(::Type{DistFix{W, F}}, success::Float64, stop::Int)

Returns a geometric distribution of the given type with the given success parameter over integers in the range [0, stop).
For more details: https://en.wikipedia.org/wiki/Geometric_distribution
"""
function geometric(::Type{DistFix{W, F}}, success::Float64, stop::Int) where {W, F}
    @assert ispow2(stop)
    bits = Int(log2(stop))
    @assert W - F > bits
    
    convert(DistFix{W, F}, DistFix{W, 0}(unit_exponential(DistFix{bits+1, bits}, log(1 - success)*2^bits).mantissa))
end

"""
    unit_gamma(::Type{DistFix{W, F}}, alpha::Int, beta::Float64; vec_arg=[], constants = [], discrete_bdd=[])

Returns a gamma distribution of the form x^α e^βx in the unit interval of the given type. The keyword arguments are there to control the order in which flips are created. 
"""
function unit_gamma(::Type{DistFix{W, F}}, alpha::Int, beta::Float64; vec_arg=[], constants = [], discrete_bdd=[]) where {W, F}
    DFiP = DistFix{W, F}
    if alpha == 0
        unit_exponential(DFiP, beta)
    elseif alpha == 1
        t = (exp(beta*2.0^(-F))*(beta*2.0^(-F) - 1) + 1)*(1 - exp(beta)) / ((1 - exp(beta*2.0^(-F)))*(exp(beta) * (beta - 1) + 1))
        coinflip = flip(t)

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
                l = discrete(DistUInt{max(Int(ceil(log(i))), 1)}, normalize(constants[count + 2:count+i+1]))
                count = count+i+1

                discrete_bdd[α - i + 1] = l
            end
            vec_expo = n_unit_exponentials(DFiP, exponential_for_gamma(α, β))

        end

        seq = Int(α*(α^2 + 5)/6)
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

"""
    general_gamma(::Type{DistFix{W, F}}, alpha::Int, beta::Float64, ll::Float64, ul::Float64)

Returns bitblast distribution for the density function x^α e^(β*x) in the range [ll, ul)
"""
function general_gamma(::Type{DistFix{W, F}}, alpha::Int, beta::Float64, ll::Float64, ul::Float64) where {W, F}
    @assert ispow2(ul - ll)
    multiply = Int(log2(ul - ll))
    start = DistFix{W, F}(ul)
    new_type = DistFix{W, F + multiply} 

    DistFix{W, F}(unit_gamma(new_type, alpha, beta).mantissa.number.bits) + start
end

####################################################
# Helper functions for `unit_gamma`
####################################################

function normalize(v)
  l = sum(v)
  [i/l for i in v]    
end

"""
Function to compute the mixing coefficients of distributions while constructing a `unit_gamma` distribution.
    α, β: x^α e^βx
    ϵ: 1/2^b depends on the type DistFix{W, F}
"""
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
        p2 = Vector(undef, α)
        for i in eachindex(c2)
            p2[i] = sum_pgp(β, ϵ, length(c2) - i) * c2[i]
        end

        vcat([p1], p2, gamma_constants(α-1, β, ϵ))
    end
end

"""
Function to compute sum of polynomial geometric series
"""
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

"""
Sum of quadratic geometric series
https://www.wolframalpha.com/input?i=sum+%28a*epsilon%29%5E2+e%5E%28beta+*+epsilon+*+a%29+from+a%3D0+to+a%3D2%5Eb-1
"""
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

"""
Sum of arithmetic geometric progression
https://www.wolframalpha.com/input?i=sum+%28a*epsilon%29+*+e%5E%28beta+*+epsilon+*+a%29+from+a%3D0+to+a%3D2%5Eb-1
"""
function sum_agp(β::Float64, ϵ::Float64)
    ans = (1/ϵ - 1)*exp(β*(1 + ϵ))
    ans -= exp(β)/ϵ
    ans += exp(β*ϵ)
    ans *= ϵ
    ans /= (exp(β*ϵ) - 1)^2
    ans
end

"""
Sum of geometric progression
https://www.wolframalpha.com/input?i=sum+e%5E%28beta+*+epsilon+*+a%29+from+a%3D0+to+a%3D2%5Eb-1
"""
function sum_gp(β::Float64, ϵ::Float64)
    ans = (exp(β) - 1) / (exp(β*ϵ) - 1)
    ans
end

"""
This function returns parameters of exponential distributions used in unit_gamma
"""
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

#############################################
# bitblasting any general distribution
#############################################

"""
    bitblast(::Type{DistFix{W,F}}, dist::ContinuousUnivariateDistribution, numpieces::Int,
        start::Float64, stop::Float64, blast_strategy=:linear; kwargs...)

The function deploys the appropriate bitblasting function based on `blast_strategy`
"""
# The following is the function for individual pieces
function bitblast(::Type{DistFix{W,F}}, dist::ContinuousUnivariateDistribution, numpieces::Int,
    start::Float64, stop::Float64, blast_strategy=:linear; kwargs...) where {W,F}
    
    if blast_strategy == :linear
        bitblast_linear(DistFix{W,F}, dist, numpieces, start, stop; kwargs...)
    elseif bitblast_strategy == :exponential
        bitblast_exponential(DistFix{W,F}, dist, numpieces, start, stop; kwargs...)
    elseif bitblast_strategy == :sample
        bitblast_sample(DistFix{W,F}, dist, numpieces, start, stop; kwargs...)
    elseif bitblast_strategy == :gamma
        error("Not implemented yet")
    else
        error("Unknown bitblasting strategy: $strategy")
    end
end

"""
    bitblast_linear(::Type{DistFix{W,F}}, dist::ContinuousUnivariateDistribution, 
        numpieces::Int, start::Float64, stop::Float64)

Returns a bitblasted representation of type `DistFix{W, F}` of the distribution `dist` using `numpieces` linear pieces in the range [start, stop) 
"""
function bitblast_linear(::Type{DistFix{W,F}}, dist::ContinuousUnivariateDistribution, 
    numpieces::Int, start::Float64, stop::Float64) where {W,F}

    # count bits and pieces
    @assert -(2^(W-F-1)) <= start < stop <= 2^(W-F-1)
    f_range_bits = log2((stop - start)*2^float(F))
    @assert isinteger(f_range_bits) "The number of $(1/2^F)-sized intervals between $start and $stop must be a power of two (not $f_range_bits)."
    @assert ispow2(numpieces) "Number of pieces must be a power of two (not $numpieces)"
    @assert numpieces < 4096 "Number of pieces is higher than 4096: might cause StackOverflowError"
    intervals_per_piece = (2^Int(f_range_bits))/numpieces
    bits_per_piece = Int(log2(intervals_per_piece))

    # truncated distribution
    dist = truncated(dist, start, stop)

    # computing numbers to construct pieces and sew them together
    total_prob = 0
    piece_probs = Vector(undef, numpieces) # prob of each piece
    border_probs = Vector(undef, numpieces) # prob of first and last interval in each piece
    linear_piece_probs = Vector(undef, numpieces) # prob of each piece if it were linear between end points

    for i=1:numpieces
        firstinter = start + (i-1)*intervals_per_piece/2^float(F) 
        lastinter = start + (i)*intervals_per_piece/2^float(F)

        piece_probs[i] = (cdf(dist, lastinter) - cdf(dist, firstinter))
        total_prob += piece_probs[i]

        border_probs[i] = [cdf(dist, firstinter + 1/2^float(F) ) - cdf(dist, firstinter), 
                cdf(dist, lastinter) - cdf(dist, lastinter - 1/2^float(F) )]
        linear_piece_probs[i] = (border_probs[i][1] + border_probs[i][2])/2 * 2^(bits_per_piece)
    end

    # coming up with discrete distribution to create a mixture of pieces
    PieceChoice = DistUInt{max(1,Int(log2(numpieces)))}
    piecechoice = discrete(PieceChoice, piece_probs ./ total_prob) # selector variable for pieces
    
    # computing flip probabilities for each flip
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

    # building each piece with uniform and triangles
    unif = uniform(DistFix{W,F},  bits_per_piece)
    tria = triangle(DistFix{W,F}, bits_per_piece)
    z = nothing
    
    for i=1:numpieces
        iszero(linear_piece_probs[i]) && continue
        firstinterval = DistFix{W,F}(start + (i-1)*2^bits_per_piece/2^float(F))
        lastinterval = DistFix{W,F}(start + (i*2^bits_per_piece-1)/2^float(F))
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

"""
    bitblast_exponential(::Type{DistFix{W,F}}, dist::ContinuousUnivariateDistribution, 
        numpieces::Int, start::Float64, stop::Float64)

Returns a bitblasted representation of type `DistFix{W, F}` of the distribution `dist` using `numpieces` exponential pieces in the range [start, stop) 
"""
function bitblast_exponential(::Type{DistFix{W,F}}, dist::ContinuousUnivariateDistribution, 
    numpieces::Int, start::Float64, stop::Float64) where {W,F}

    # count bits and pieces
    @assert -(2^(W-F-1)) <= start < stop <= 2^(W-F-1)
    f_range_bits = log2((stop - start)*2^float(F))
    @assert isinteger(f_range_bits) "The number of $(1/2^F)-sized intervals between $start and $stop must be a power of two (not $f_range_bits)."
    @assert ispow2(numpieces) "Number of pieces must be a power of two (not $numpieces)"
    intervals_per_piece = (2^Int(f_range_bits))/numpieces

    # truncated distribution
    d = truncated(dist, start, stop)

    # computing numbers to construct pieces and sew them together
    total_prob = 0
    piece_probs = Vector(undef, numpieces)
    expo_beta = Vector(undef, numpieces)

    for i=1:numpieces
        firstinter = start + (i-1)*intervals_per_piece/2.0^(F)
        lastinter = start + (i)*intervals_per_piece/2.0^(F)
    
        expo_beta[i] = beta(d, firstinter, lastinter, 2.0^(-F))
    
        piece_probs[i] = (cdf.(d, lastinter) - cdf.(d, firstinter))
        total_prob += piece_probs[i]
    end

    # coming up with discrete distribution to create a mixture of pieces
    PieceChoice = DistUInt{max(1,Int(log2(numpieces)))}
    piecechoice = discrete(PieceChoice, piece_probs ./ total_prob) # selector variable for pieces
    z = nothing

    for i=1:numpieces
        expo_dist = exponential(DistFix{W, F}, expo_beta[i], start + (i-1)*intervals_per_piece/2^float(F), start + (i)*intervals_per_piece/2.0^(F))
        z = if isnothing(z)
                expo_dist
            else
                ifelse(prob_equals(piecechoice, PieceChoice(i-1)), expo_dist, z)  
            end  
    end
    return z
end

"""
    bitblast_sample(::Type{DistFix{W,F}}, dist::ContinuousUnivariateDistribution, 
        numpieces::Int, start::Float64, stop::Float64, offset::Float64, width::Float64)

A modified version of the function bitblast that works with the assumption of lower bits being sampled.
"""
function bitblast_sample(::Type{DistFix{W,F}}, dist::ContinuousUnivariateDistribution, 
    numpieces::Int, start::Float64, stop::Float64; offset::Float64=0.0, width::Float64=1/2^float(F)) where {W,F}

    # count bits and pieces
    @assert -(2^(W-F-1)) <= start < stop <= 2^(W-F-1)
    f_range_bits = log2((stop - start)*2.0^F)
    @assert isinteger(f_range_bits) "The number of $(1/2^F)-sized intervals between $start and $stop must be a power of two (not $f_range_bits)."
    @assert ispow2(numpieces) "Number of pieces must be a power of two (not $numpieces)"
    intervals_per_piece = (2^Int(f_range_bits))/numpieces
    bits_per_piece = Int(log2(intervals_per_piece))

    # truncated distribution
    dist = truncated(dist, start, stop)

    # computing numbers to construct pieces and sew them together
    total_prob = 0
    piece_probs = Vector(undef, numpieces) # prob of each piece
    border_probs = Vector(undef, numpieces) # prob of first and last interval in each piece
    linear_piece_probs = Vector(undef, numpieces) # prob of each piece if it were linear between end points

    for i=1:numpieces
        firstinter = start + (i-1)*intervals_per_piece/2.0^F 
        lastinter = start + (i)*intervals_per_piece/2.0^F 

        # Warning: A potential source of terrible runtime
        piece_probs[i] = 0
        for j=1:intervals_per_piece
            piece_probs[i] += cdf(dist, firstinter + offset + width + (j-1)/2.0^F) - cdf(dist, firstinter + offset + (j-1)/2.0^F)
        end
        total_prob += piece_probs[i]

        border_probs[i] = [cdf(dist, firstinter + offset+width) - cdf(dist, firstinter + offset), 
                                cdf(dist, lastinter -1/2.0^F + offset+width) - cdf(dist, lastinter - 1/2.0^F + offset)]
        linear_piece_probs[i] = (border_probs[i][1] + border_probs[i][2])/2 * 2^(bits_per_piece)
    end

    # coming up with discrete distribution to create a mixture of pieces
    PieceChoice = DistUInt{max(1,Int(log2(numpieces)))}
    piecechoice = discrete(PieceChoice, piece_probs ./ total_prob) # selector variable for pieces

    # computing flip probabilities for each piece
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

    # building each piece with uniform and triangles
    unif = uniform(DistFix{W,F},  bits_per_piece)
    tria = triangle(DistFix{W,F}, bits_per_piece)
    z = nothing

    for i=1:numpieces
        iszero(linear_piece_probs[i]) && continue
        firstinterval = DistFix{W,F}(start + (i-1)*2^bits_per_piece/2.0^F)
        lastinterval = DistFix{W,F}(start + (i*2^bits_per_piece-1)/2.0^F)
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

###################################
# Helper functions for bitblasting
###################################

function beta(d::ContinuousUnivariateDistribution, start::Float64, stop::Float64, interval_sz::Float64)
    prob_start = cdf(d, start + interval_sz) - cdf(d, start)
    if prob_start == 0.0
        prob_start = eps(0.0)
    end
    prob_end = cdf(d, stop) - cdf(d, stop - interval_sz)
    result = (log(prob_end) - log(prob_start)) / (stop - start - interval_sz)
    result
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

# # TODO: Write tests for the following function
# function unit_concave(t::Type{DistFix{W, F}}, beta::Float64) where {W, F}
#     @assert beta <= 0
#     DFiP = DistFix{W, F}
#     Y = uniform(DFiP, 0.0, 1.0)
#     X = unit_exponential(DFiP, beta)
#     observe((X < Y)| prob_equals(X, Y))
#     Y
# end