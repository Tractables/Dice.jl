using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir
using Distributions

code = @dice begin
        
    function uniform(b::Int, t::Type{T}) where T
        x = Vector(undef, b)
        for i = b:-1:1
            x[i] = flip(0.5)
        end
        return T(x)
    end

    function triangle(b::Int, t::Type)
        s = false
        n = 2^b
        x = Vector(undef, b)
        y = Vector(undef, b)
        for i = b:-1:1
            x[i] = Dice.ifelse(s, flip(1/2), flip((3n - 2)/ (4n-4)))
            y[i] = flip((n-2)/(3n-2))
            s = s || (x[i] && !y[i])
            n = n/2
        end
        return t(x)
    end

    function discrete(p::Vector{Float64}, t::Type)
        mb = length(p)
        @assert sum(p) ≈ 1
        v = zeros(mb)
        sum_ = 1
        for i=1:mb
            # @show p[i], sum_
            # @show p[i] ≈ sum_
            if (p[i] >= sum_)
                v[i] = 1
                break
            else
                v[i] = p[i]/sum_
            end
            sum_ = sum_ - p[i]
            # @show v[i]
            @assert v[i] >= 0
            @assert v[i] <= 1
        end

        ans = t(dicecontext(), mb-1)
        for i=mb-1:-1:1
            ans = if flip(v[i]) t(dicecontext(), i-1) else ans end
        end
        return ans
    end

    function discrete2(p::Vector{Float64}, t::Type)

        function recurse(p::Vector, i, s, e, prob::Vector)
            if (i == 0)
                flip(sum(prob[Int((s+e+1)/2):e])/sum(prob[s:e]))
            else
                (if p[length(p) - i + 1] recurse(p, i-1, Int((s+e+1)/2), e, prob) else recurse(p, i-1, s, Int((s+e-1)/2), prob) end)
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
        t(reverse(int_vector))
    end

    function anyline(bits::Int, p::Float64, t::Type)
        # @show p*2^bits
        @assert p*2^bits >= 0
        @assert p*2^bits <= 1
        ans = Dice.ifelse(flip(p*2^bits), uniform(bits, t), triangle(bits, t))
        return ans
    end

    function max_index_not1(prob::Vector, piece::Vector)
        max = 0
        for i=1:length(prob)
            if piece[i] == 1
                continue
            else
                if (max == 0)
                    max = i
                else
                    if prob[i] > prob[max]
                        max = i
                    else
                        max = max
                    end
                end
            end
        end
        # @assert max != 0
        max
    end 


    function piece_dist(pieces::Int, t::Type{DistFixParam{T, F}}, d::ContinuousUnivariateDistribution) where {T, F}
        # d = Normal(mean, std)
        @assert pieces <= 2^(T-1)
        d = Truncated(d, 0, 2^(T-F))
        piece_size = [T]
        # @show piece_size
        while (length(piece_size) < pieces)
            prob = []
            lower = 0
            upper = 0
            for i = 1:length(piece_size)
                # @show lower
                upper = lower + 2^piece_size[i]/2^(F)
                # @show upper
                # @show cdf(d, upper) - cdf(d, lower)
                append!(prob, cdf(d, upper) - cdf(d, lower))
                lower = upper
            end
            # @show prob
            lastindex = length(prob)
            for j=length(prob):-1:1
                if prob[j] ≈ 0
                    lastindex -=1
                else
                    break
                end
            end


            a = max_index_not1(prob[1:lastindex], piece_size[1:lastindex])
            if a == 0
                break
            else
                
                # @show a
                piece_size = vcat(piece_size[1:a-1], [piece_size[a]-1, piece_size[a]-1], piece_size[a+1: lastindex])
                # @show piece_size
            end
        end
        piece_size
    end

    function continuous(pieces::Int, t::Type{DistFixParam{T, F}}, d::ContinuousUnivariateDistribution) where {T, F}
        d = Truncated(d, 0, 2^(T-F))
        whole_bits = T
        point = F

        # @show whole_bits, point
        start = 0
        interval_sz = piece_dist(pieces, t, d)
        # interval_sz = Vector{Int64}([1, 1, 1, 1, 1, 1])
        pieces = length(interval_sz)
        # @show pieces
        areas = Vector(undef, pieces)
        total_area = 0
    
        end_pts = Vector(undef, pieces)
        for i=1:pieces
            p1 = start
            p2 = p1 + 1/2^point
            p3 = start + 2^interval_sz[i]/2^point
            p4 = p3 - 1/2^point
            # @show p1, p2, p3, p4
            pts = [cdf.(d, p2) - cdf.(d, p1), cdf.(d, p3) - cdf.(d, p4)]
            end_pts[i] = pts
    
            areas[i] = (pts[1] + pts[2])*2^(interval_sz[i] - 1)
            total_area += areas[i]
            start = start + 2^interval_sz[i]/2^point
        end

        # @show areas

        rel_prob = areas/total_area
        # @show rel_prob

        b = discrete2(rel_prob, DistInt)
        unif = uniform(maximum(interval_sz), t).number.bits
                
        a = end_pts[pieces][1]/areas[pieces]
        # @show a
        # l = a > 1/2^bits

        ans = t(dicecontext(), 2^whole_bits-1)
  
        # @show bits
        position = 0
        for i=1:length(interval_sz)
            position += 2^interval_sz[i]
        end
        # @show position
        for i=pieces:-1:1
            if (areas[i] == 0)
                a = 0.0

            else
                a = end_pts[i][1]/areas[i]
            end
            # @show a
            l = a > 1/2^interval_sz[i]
            # @show bits
            # @show a
            # @show i
            position -= 2^interval_sz[i]
            # @show a * 2^interval_sz[i]
            # @show position
            ans = 
                if prob_equals(b, i-1) 
                    (if l
                        # @show position + 2^interval_sz[i]
                        @show position + 2^interval_sz[i] - 1
                        t(dicecontext(), position + 2^interval_sz[i] - 1) - 
                        # anyline(interval_sz[i], 2/2^interval_sz[i] - a, t)
                        Dice.ifelse(flip(2 - a*2^interval_sz[i]), t(unif[1:interval_sz[i]]), triangle(interval_sz[i], t))
                    else
                        # @show position
                        @show position
                        t(dicecontext(), position) + 
                            # anyline(interval_sz[i], a, t)
                            Dice.ifelse(flip(a*2^interval_sz[i]), t(unif[1:interval_sz[i]]), triangle(interval_sz[i], t))
                    end)[1]
                else
                    ans
                end  
        end
        return ans
    end

    # uniform(2, DistInt)
    # triangle(2, DistInt)
    # anyline(2, 0.1, DistInt)
    # discrete([0.1, 0.2, 0.3, 0.4], DistInt)
    # (continuous(4, DistFixParam{10, 7}, Normal(1, 0.25)) + continuous(4, DistFixParam{10, 7}, Normal(1, 0.25)))[1]
    # continuous(4, DistFixParam{4, 3}, Beta(1, 1))
    # continuous(4, DistFixParam{4, 2}, Exponential(1))
    continuous(8, DistFixParam{4, 0}, Normal(8, 2))
end



bdd = compile(code)
a = (infer(code, :bdd))


num_flips(bdd)
num_nodes(bdd)

function KL_div(a, T, F, d::ContinuousUnivariateDistribution)
    d = Truncated(d, 0, 2^(T-F))
    lower = 0
    upper = lower + 2^F
    p = Vector{Float64}(undef, 2^T)
    for i=1:2^T
        p[i] = cdf(d, upper) - cdf(d, lower)
        lower = upper
        upper = lower + 2^F
    end
    
    p[1:length(a)]
    # @show sum(map(a->a[2], a))
    # @show p
    # @show length(a)
    # ans = Vector(undef, length(a))
    # for i=1:length(a)
    #     ans[i] = p[i]*(log(p[i]) - log(a[i][2]))
    # end
    # ans
    kldivergence(p, map(a->a[2], a))
    # chebyshev(p, map(a->a[2], a))
end

d = KL_div(a, 4, 0, Normal(8, 2))