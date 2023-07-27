using Distributions
using SymPy
@vars varint
@vars v2

export DistFixedPoint, continuous, unit_exponential, exponential, laplace, unit_gamma, shift_point_gamma, sum_pgp

##################################
# types, structs, and constructors
##################################

struct DistFixedPoint{W, F} <: Dist{Number}
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
    @assert i >= -2^(W-F-1)
    @assert i < 2^(W-F-1)
    new_i = Int(floor(if i >= 0 i*2^F else i*2^F + 2^W end))
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
# # moments
# ##################################

function expectation(x::DistFixedPoint{W, F}; kwargs...) where W where F
    expectation(x.number; kwargs...)/2^F
end

function variance(x::DistFixedPoint{W, F}; kwargs...) where W where F
    variance(x.number; kwargs...)/2^(2*F)
end
    

# ##################################
# # methods
# ##################################

bitwidth(::DistFixedPoint{W, F}) where W where F = W

function uniform(::Type{DistFixedPoint{W, F}}, n = W) where W where F
    DistFixedPoint{W, F}(DistInt{W}(uniform(DistUInt{W}, n).bits))
end

function uniform(t::Type{DistFixedPoint{W, F}}, start::Float64, stop::Float64; kwargs...) where W where F
    @assert start >= -(2^(W - F - 1))
    @assert stop <= (2^(W - F - 1))
    @assert start < stop
    a = Int(round((stop - start)*2^F))
    return DistFixedPoint{W, F}(uniform(DistInt{W}, 0, a; kwargs...)) + DistFixedPoint{W, F}(start)
 end
 

function triangle(t::Type{DistFixedPoint{W, F}}, b::Int) where W where F
    @assert b <= W
    DistFixedPoint{W, F}(triangle(DistInt{W}, b))
end

##################################
# casting
##################################

function Base.convert(::Type{DistFixedPoint{W2, F2}}, x::DistFixedPoint{W1, F1}) where W1 where W2 where F1 where F2
    #TODO: check if cases are exhaustive
    if (F1 == F2)
        DistFixedPoint{W2, F2}(convert(DistInt{W2}, x.number))
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

function Base.isless(x::DistFixedPoint{W, F}, y::DistFixedPoint{W, F}) where W where F
    isless(x.number, y.number)
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
    x1 = convert(DistFixedPoint{W+F, F}, x)
    y1 = convert(DistFixedPoint{W+F, F}, y)
    prodint = x1.number * y1.number
    prodfip = DistFixedPoint{W+F, 2F}(prodint)
    convert(DistFixedPoint{W, F}, prodfip)
end

function Base.:(/)(x::DistFixedPoint{W, F}, y::DistFixedPoint{W, F}) where {W, F}
    xp = convert(DistFixedPoint{W+F, 2*F}, x)
    yp = convert(DistFixedPoint{W+F, F}, y)
    ans = xp.number / yp.number

    n_overflow = DistInt{F+1}(ans.number.bits[1:F+1])
    overflow = !prob_equals(n_overflow, DistInt{F+1}(-1)) & !iszero(n_overflow)
    errorcheck() & overflow && error("integer overflow")

    DistFixedPoint{W, F}(ans.number.bits[F+1:W+F])
end

#################################
# continuous distributions
#################################
  
function continuous_linear(t::Type{DistFixedPoint{W, F}}, d::ContinuousUnivariateDistribution, pieces::Int, start::Float64, stop::Float64) where {W, F}

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
    @show start, stop
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

###########################
# LExBit
###########################

function unit_exponential(t::Type{DistFixedPoint{W, F}}, beta::Float64) where W where F
    DistFixedPoint{W, F}(vcat([false for i in 1:W-F], [flip(exp(beta/2^i)/(1+exp(beta/2^i))) for i in 1:F]))
end

function exponential(t::Type{DistFixedPoint{W, F}}, beta::Float64, start::Float64, stop::Float64) where W where F   
    range = stop - start
    @assert ispow2(range)

    new_beta = beta*range

    bits = Int(log2(range)) + F
    # for i in 1:bits
    #     @show exp(new_beta/2^i)/(1+exp(new_beta/2^i))
    # end
    # @show beta
    # @show new_beta
    # @show [exp(new_beta/2^i)/(1+exp(new_beta/2^i)) for i in 1:bits]
    bit_vector = vcat([false for i in 1:W - bits], [flip(exp(new_beta/2^i)/(1+exp(new_beta/2^i))) for i in 1:bits])

    DistFixedPoint{W, F}(bit_vector) + DistFixedPoint{W, F}(start)
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

function continuous_exp(t::Type{DistFixedPoint{W, F}}, d::ContinuousUnivariateDistribution, pieces::Int, start::Float64, stop::Float64) where {W, F}

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
    total_area = 0

    beta_vec = Vector(undef, pieces)
    start_pts = Vector(undef, pieces)
    stop_pts = Vector(undef, pieces)

    

    # Figuring out end points
    for i=1:pieces
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

    ans = DistFixedPoint{W, F}((2^(W-1)-1)/2^F)

    for i=pieces:-1:1
        ans = ifelse( prob_equals(b, DistUInt{piece_bits}(i-1)), 
                exponential(DistFixedPoint{W, F}, beta_vec[i], start_pts[i], stop_pts[i]),
                ans)  
    end
    return ans
end

function continuous(t::Type{DistFixedPoint{W, F}}, d::ContinuousUnivariateDistribution, pieces::Int, start::Float64, stop::Float64, exp::Bool=false) where {W, F}
    c = if exp
        continuous_exp(DistFixedPoint{W, F}, d, pieces, start, stop)
    else 
        continuous_linear(DistFixedPoint{W, F}, d, pieces, start, stop)
    end
    return c
end

# https://en.wikipedia.org/wiki/Laplace_distribution
function laplace(t::Type{DistFixedPoint{W, F}}, mean::Float64, scale::Float64, start::Float64, stop::Float64) where {W, F}
    @assert scale > 0

    beta1 = -1/scale
    e1 = exponential(DistFixedPoint{W, F}, beta1, mean, stop)

    beta2 = 1/scale
    e2 = exponential(DistFixedPoint{W, F}, beta2, start, mean)

    ifelse(flip(0.5), e1, e2)
end

#Helper function that returns exponentials 

function shift_point_gamma(::Type{DistFixedPoint{W, F}}, alpha::Int, beta::Float64) where {W, F}
    DFiP = DistFixedPoint{W, F}
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

function n_unit_exponentials(::Type{DistFixedPoint{W, F}}, betas::Vector{Float64}) where {W, F}
    DFiP = DistFixedPoint{W, F}
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
    for i in 1:F
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
    @vars varint
    @vars v2
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




function unit_gamma(t::Type{DistFixedPoint{W, F}}, alpha::Int, beta::Float64; vec_arg=[], constants = [], discrete_bdd=[]) where {W, F}
    DFiP = DistFixedPoint{W, F}
    if alpha == 0
        unit_exponential(DFiP, beta)
    elseif alpha == 1
        if (length(vec_arg) != 0)
            (Y, Z, U) = vec_arg
        else
            (Y, Z, U) = n_unit_exponentials(DFiP, [beta, beta, 0.0])
        end
        observe(U < Y)

        t = (exp(beta*2.0^(-F))*(beta*2.0^(-F) - 1) + 1)*(1 - exp(beta)) / ((1 - exp(beta*2.0^(-F)))*(exp(beta) * (beta - 1) + 1))
        
        final = ifelse(flip(t), Z, Y)
        final
    else 
        α = alpha
        β = beta
        if (length(vec_arg) != 0)
            vec_expo = vec_arg
            
        else
            discrete_bdd = Vector(undef, α)
            constants = gamma_constants(alpha, beta, 1/2^F)
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
# function unit_concave(t::Type{DistFixedPoint{W, F}}, beta::Float64) where {W, F}
#     @assert beta <= 0
#     DFiP = DistFixedPoint{W, F}
#     Y = uniform(DFiP, 0.0, 1.0)
#     X = unit_exponential(DFiP, beta)
#     observe((X < Y)| prob_equals(X, Y))
#     Y
# end
