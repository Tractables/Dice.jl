using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir
using Distributions

code = @dice begin
        
    function uniform(b::Int, t::Type)
        x = Vector(undef, b)
        for i = b:-1:1
            x[i] = flip(0.5)
        end
        return t(x)
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
            if (p[i] >= sum_)
                v[i] = 1
                break
            else
                v[i] = p[i]/sum_
            end
            sum_ = sum_ - p[i]
            @show v[i]
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
                (Dice.ifelse(p[length(p) - i + 1], recurse(p, i-1, Int((s+e+1)/2), e, prob), recurse(p, i-1, s, Int((s+e-1)/2), prob)))
            end
        end

        mb = length(p)
        add = Int(ceil(log2(mb)))
        p_proxy = vcat(p, zeros(2^add - mb))
        int_vector = []
        
        for i=1:add
            @show i
            a = recurse(int_vector, i-1, 1, 2^add, p_proxy)
            push!(int_vector, a)
        end
        if add == 0 t(0) else t(reverse(int_vector)) end
    end

    function anyline(bits::Int, p::Float64, t::Type)
        # @show p*2^bits
        @assert p*2^bits >= 0
        @assert p*2^bits <= 1
        ans = Dice.ifelse(flip(p*2^bits), uniform(bits, t), triangle(bits, t))
        return ans
    end

    function continuous(pieces::Int, t::Type{DistFixParam{T, F}}, d::ContinuousUnivariateDistribution) where {T, F}

        whole_bits = T
        point = F
        
        start = 0
        interval_sz = (2^whole_bits/pieces)
        bits = Int(log2(interval_sz))
    
        areas = Vector(undef, pieces)
        total_area = 0
    
        end_pts = Vector(undef, pieces)
        for i=1:pieces
            p1 = start + (i-1)*interval_sz/2^point
            p2 = p1 + 1/2^point
            p3 = start + (i)*interval_sz/2^point
            p4 = p3 - 1/2^point
    
            pts = [cdf.(d, p2) - cdf.(d, p1), cdf.(d, p3) - cdf.(d, p4)]
            end_pts[i] = pts
    
            areas[i] = (pts[1] + pts[2])*2^(bits - 1)
            total_area += areas[i]
        end

        rel_prob = areas/total_area

        a = Vector(undef, pieces)
        l = Vector(undef, pieces)
        ex= Vector(undef, pieces)
        
        for i=pieces:-1:1
            if (areas[i] == 0)
                a[i] = 0.0
            else
                a[i] = end_pts[i][1]/areas[i]
            end
            if a[i] > 1/2^bits
                l[i] = -
                ex[i] = i*2^bits - 1
                a[i] = 2/2^bits - a[i]
            else
                l[i] = +
                ex[i] = (i-1)*2^bits
            end
        end

        
        
        # unif = uniform(bits, t)
        
        b = discrete2(rel_prob, DistInt)
        flip_vector = Vector(undef, pieces)
        for i = 1:pieces
            flip_vector[i] = flip(a[i]*2^bits)
        end
        unif = uniform(bits, t)
        tria = triangle(bits, t)


        # ans = l[pieces](t(dicecontext(), ex[pieces]), Dice.ifelse(flip_vector[pieces], unif, tria))[1]
        ans = t(dicecontext(), 2^whole_bits - 1)
    
        for i=pieces:-1:1
            ans = if prob_equals(b, i-1) 
                    (l[i](t(dicecontext(), ex[i]), 
                        (if flip_vector[i] unif else tria end)))[1]
                        # (anyline(bits, a[i], t))))[1]
                else
                    ans
                end  
        end
        return ans
    end

    (continuous(16, DistFixParam{8, 0}, Normal(8, 2)))
end



bdd = compile(code)
a = (infer(code, :bdd))


num_flips(bdd)
num_nodes(bdd)    