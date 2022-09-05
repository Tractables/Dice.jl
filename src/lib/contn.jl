using Distributions

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
    b = discrete2(mgr, rel_prob, DistUInt)

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

function continuous(mgr, pieces::Int, t::Type{DistSigned{T, F}}, d::ContinuousUnivariateDistribution, flag::Int, shift::Int, f) where {T, F}
    # println("Signed continuous")
    d = Truncated(d, -(2^(T-1-F)) - shift*1/2^(F+1), (2^(T-1-F)) - shift*1/2^(F+1))
    whole_bits = T
    point = F

    start = -(2^(T-1-F)) - shift*1/2^(F+1)
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

        @show p1, p2, p3, p4

        p1 = f(p1)
        p2 = f(p2)
        p3 = f(p3)
        p4 = f(p4)

        if flag == 0
            @show p1, p2, p3, p4
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
        @show p1, p2, p3, p4, areas[i]

        total_area += areas[i]
    end

    rel_prob = areas/total_area

    @show rel_prob
    @show areas


    # @show areas
    b = discrete2(mgr, rel_prob, DistUInt)
    
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
            @show 2 - a*2^bits, i, areas[i]
            piece_flips[i] = DistBool(mgr, 2 - a*2^bits)
        else
            @show a*2^bits
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

function continuous(mgr, pieces::Int, t::Type{DistFixParam{T, F}}, d::ContinuousUnivariateDistribution, flag::Bool, flag2::Bool, f) where {T, F}
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

        @show p1, p2, p3, p4
        p1 = f(p1)
        p2 = f(p2)
        p3 = f(p3)
        p4 = f(p4)
        @show p1, p2, p3, p4


        pts = [cdf.(d, p2) - cdf.(d, p1), cdf.(d, p3) - cdf.(d, p4)]
        end_pts[i] = pts

        trap_areas[i] = (pts[1] + pts[2])*2^(bits - 1)
        areas[i] = (cdf.(d, p3) - cdf.(d, p1))

        total_area += areas[i]
    end

    
    rel_prob = areas/total_area
    @show rel_prob
    @show end_pts
    @show trap_areas


    # @show rel_prob
    b = discrete2(mgr, rel_prob, DistUInt)

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