using Distributions

export uniform, triangle, discrete2, anyline, continuous, shifted_continuous

function uniform(mgr, b::Int, t::Type)
    x = Vector(undef, b)
    for i = b:-1:1
        x[i] = DistBool(mgr, 0.5)
    end
    return t(x)
end

function triangle(mgr, b::Int, t::Type)
    s = false
    n = 2^b
    x = Vector(undef, b)
    y = Vector(undef, b)
    for i = b:-1:1
        x[i] = Dice.ifelse(s, DistBool(mgr, 1/2), DistBool(mgr, (3n - 2)/ (4n-4)))
        y[i] = DistBool(mgr, (n-2)/(3n-2))
        s = s | (x[i] & !y[i])
        n = n/2
    end
    return t(x)
end

function discrete2(mgr, p::Vector{Float64}, t::Type)
    @assert sum(p) ≈ 1

    function recurse(p::Vector, i, s, e, prob::Vector)
        if (i == 0)
            a = sum(prob[s:e])
            if a == 0
                DistBool(mgr, false)
            else
                DistBool(mgr, sum(prob[Int((s+e+1)/2):e])/sum(prob[s:e]))
            end
        else
            (Dice.ifelse(p[length(p) - i + 1], recurse(p, i-1, Int((s+e+1)/2), e, prob), recurse(p, i-1, s, Int((s+e-1)/2), prob)))
            # if p[length(p) - i + 1] recurse(p, i-1, Int((s+e+1)/2), e, prob) else recurse(p, i-1, s, Int((s+e-1)/2), prob) end
            
        end
    end

    mb = length(p)
    add = Int(ceil(log2(mb)))
    p_proxy = vcat(p, zeros(2^add - mb))
    int_vector = []
    
    for i=1:add
        # @show i
        a = recurse(int_vector, i-1, 1, 2^add, p_proxy)
        push!(int_vector, a)
    end
    if add == 0 t(mgr, 0) else t(reverse(int_vector)) end
end

function anyline(mgr, bits::Int, p::Float64, t::Type)
    @assert p*2^bits >= 0
    @assert p*2^bits <= 1
    # @show p
    ans = Dice.ifelse(DistBool(mgr, p*2^bits), uniform(mgr, bits, t), triangle(mgr, bits, t))
    return ans
end

function shifted_continuous(mgr, pieces::Int, t::Type{DistFixParam{T, F}}, d::ContinuousUnivariateDistribution) where {T, F}
    d = Truncated(d, 0 - 1/2^(F + 1), 2^(T-F) - 1/2^(F + 1))
    whole_bits = T
    point = F

    start = 0
    interval_sz = (2^whole_bits/pieces)

    # @show interval_sz
    # @show interval_sz * pieces/2^F

    while (cdf.(d, interval_sz*pieces/2^F) - cdf.(d, interval_sz*pieces/2^(F+1)) ≈ 0) & (interval_sz > 2)
        interval_sz /= 2
        @show interval_sz
    end

    # @show interval_sz

    
    
    bits = Int(log2(interval_sz))
    areas = Vector(undef, pieces)
    trap_areas = Vector(undef, pieces)
    total_area = 0

    end_pts = Vector(undef, pieces)
    for i=1:pieces
        p1 = start + (i-1)*interval_sz/2^point - 1/2^(F + 1)
        p2 = p1 + 1/2^(point) 
        p3 = start + (i)*interval_sz/2^point - 1/2^(F + 1)
        p4 = p3 - 1/2^point 

        # @show p1, p2, p3, p4

        pts = [cdf.(d, p2) - cdf.(d, p1), cdf.(d, p3) - cdf.(d, p4)]
        end_pts[i] = pts

        trap_areas[i] = (pts[1] + pts[2])*2^(bits - 1)
        areas[i] = (cdf.(d, p3) - cdf.(d, p1))

        total_area += areas[i]
    end

    rel_prob = areas/total_area

    tria = triangle(mgr, bits, t)
    unif = uniform(mgr, bits, t)
    # @show rel_prob
    b = discrete2(mgr, rel_prob, DistInt)

    ans = t(mgr, (2^whole_bits-1)/2^F)

    for i=pieces:-1:1
        if (trap_areas[i] == 0)
            a = 0.0
        else
            a = end_pts[i][1]/trap_areas[i]
        end
        # @show i, a
        # @show bits
        # @assert 2 - a*2^bits >= 0
        l = a > 1/2^bits
        
        # @show a
        # @show i
        # @show a*2^bits
        ans = Dice.ifelse( prob_equals(b, i-1), 
                (if l
                    # @show i*2^bits-1
                    t(mgr, ((i)*2^bits - 1)/2^F) - 
                    anyline(mgr, bits, 2/2^bits - a, t)
                    # Dice.ifelse(flip(2 - a*2^bits), unif, tria)
                else
                    # @show (i-1)*2^bits
                    t(mgr, (i - 1)*2^bits/2^F) + 
                        anyline(mgr, bits, a, t)
                        # Dice.ifelse(flip(a*2^bits), unif, tria)
                end)[1],
                ans)  
    end
    return ans
end

function continuous(mgr, pieces::Int, t::Type{DistSigned{T, F}}, d::ContinuousUnivariateDistribution, flag::Int) where {T, F}
    # println("Signed continuous")
    d = Truncated(d, -(2^(T-1-F)), (2^(T-1-F)))
    whole_bits = T
    point = F

    start = -(2^(T-1-F))
    interval_sz = (2^whole_bits/pieces)

    # while (cdf.(d, start + interval_sz*pieces/2^F) - cdf.(d, start + interval_sz*pieces/2^(F+1)) ≈ 0) & (interval_sz > 2)
        # interval_sz /= 2
        # @show interval_sz
    # end

    bits = Int(log2(interval_sz))
    areas = Vector(undef, pieces)
    trap_areas = Vector(undef, pieces)
    total_area = 0

    end_pts = Vector(undef, pieces)
    for i=1:pieces
        p1 = start + (i-1)*interval_sz/2^point 
        p2 = p1 + 1/2^(point) 
        p3 = start + (i)*interval_sz/2^point 
        p4 = p3 - 1/2^point 

        if flag == 0
            # probability mass at end points
            pts = [cdf.(d, p2) - cdf.(d, p1), cdf.(d, p3) - cdf.(d, p4)]
        elseif flag == 1
            # pdfs at the end points p1 and p3
            pts = [pdf(d, p1), pdf(d, p3)]
        elseif flag == 2
            # pdfs at the end points p1 and p4
            pts = [pdf(d, p1), pdf(d, p4)]
        else
            # probability mass of two halves
            pts = [cdf(d, (p1+p3)/2) - cdf(d, p1), cdf(d, p3) - cdf(d, (p1+p3)/2)]
        end
        end_pts[i] = pts

        #TODO: figure out the correct expression for trap_areas for different end points
        trap_areas[i] = (pts[1] + pts[2])*2^(bits - 1)
        areas[i] = (cdf.(d, p3) - cdf.(d, p1))
        # @show p1, p3

        total_area += areas[i]
    end

    rel_prob = areas/total_area


    # @show areas
    b = discrete2(mgr, rel_prob, DistInt)
    
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
            piece_flips[i] = DistBool(mgr, 2 - a*2^bits)
        else
            piece_flips[i] = DistBool(mgr, a*2^bits)
        end  
    end

    unif = uniform(mgr, bits, t)
    tria = triangle(mgr, bits, t)
    ans = t(mgr, (2^(T-1)-1)/2^F)

    for i=pieces:-1:1
        ans = Dice.ifelse( prob_equals(b, i-1), 
                (if l_vector[i]
                    Dice.ifelse(piece_flips[i], 
                    (t(mgr, (i - 1)*2^bits/2^F - 2^(T - 1 - F)) + unif)[1], 
                    (t(mgr, (i*2^bits - 1)/2^F - 2^(T-1 - F)) - tria)[1])
                else
                    (t(mgr, (i - 1)*2^bits/2^F - 2^(T - 1 - F)) + 
                        Dice.ifelse(piece_flips[i], unif, tria))[1]
                    
                end),
                ans)  
    end
    return ans
end

function continuous(mgr, pieces::Int, t::Type{DistFixParam{T, F}}, d::ContinuousUnivariateDistribution, flag::Bool, flag2::Bool) where {T, F}
    #initializing basics
    d = Truncated(d, 0, 2^(T-F))
    whole_bits = T
    point = F
    start = 0
    interval_sz = (2^whole_bits/pieces)

    #refining interval size
    while (cdf.(d, interval_sz*pieces/2^F) - cdf.(d, interval_sz*pieces/2^(F+1)) ≈ 0) & (interval_sz > 2)
        interval_sz /= 2
        @show interval_sz
    end

    #initializing 
    bits = Int(log2(interval_sz))
    areas = Vector(undef, pieces)
    trap_areas = Vector(undef, pieces)
    total_area = 0
    end_pts = Vector(undef, pieces)

    #calculating end points and probabilities
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

        total_area += areas[i]
    end

    rel_prob = areas/total_area


    # @show rel_prob
    b = discrete2(mgr, rel_prob, DistInt)

    piece_flips = Vector(undef, pieces)
    for i=pieces:-1:1
        if (trap_areas[i] == 0)
            a = 0.0
        else
            a = end_pts[i][1]/trap_areas[i]
        end
        l = a > 1/2^bits
        if l
            piece_flips[i] = DistBool(mgr, 2 - a*2^bits)
        else
            piece_flips[i] = DistBool(mgr, a*2^bits)
        end  
    end

    unif = uniform(mgr, bits, t)
    tria = triangle(mgr, bits, t)

    ans = t(mgr, (2^whole_bits-1)/2^F)

    for i=pieces:-1:1
        if (trap_areas[i] == 0)
            a = 0.0
        else
            a = end_pts[i][1]/trap_areas[i]
        end

        l = a > 1/2^bits
                
        ans = Dice.ifelse( prob_equals(b, i-1), 
                (if l
                    (if flag 
                        (t(mgr, (i*2^bits - 1)/2^F) - anyline(mgr, bits, 2/2^bits - a, t))[1]
                    else
                        Dice.ifelse(piece_flips[i], 
                                    (t(mgr, (i - 1)*2^bits/2^F) + unif)[1], 
                                    (t(mgr, (i*2^bits - 1)/2^F) - tria)[1])
                    end)
                else
                    (t(mgr, (i - 1)*2^bits/2^F) 
                    + 
                    (if flag 
                        anyline(mgr, bits, a, t)
                    else
                        Dice.ifelse(piece_flips[i], unif, tria)
                    end))[1]
                end),
                ans) 
    end
    return ans
end



