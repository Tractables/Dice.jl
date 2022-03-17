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
        # @show sum(p)
        @assert sum(p) ≈ 1
        v = zeros(mb)
        sum_ = 1
        for i=1:mb
            # @show p[i], sum_
            # @show p[i] ≈ sum_
            if (p[i] > sum_)
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
                # (Dice.ifelse(p[length(p) - i + 1], recurse(p, i-1, Int((s+e+1)/2), e, prob), recurse(p, i-1, s, Int((s+e-1)/2), prob)))
                if p[length(p) - i + 1] recurse(p, i-1, Int((s+e+1)/2), e, prob) else recurse(p, i-1, s, Int((s+e-1)/2), prob) end
                
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
        t(reverse(int_vector))
    end

    function anyline(bits::Int, p::Float64, t::Type)
        # @show p*2^bits
        @assert p*2^bits >= 0
        @assert p*2^bits <= 1
        ans = Dice.ifelse(flip(p*2^bits), uniform(bits, t), triangle(bits, t))
        return ans
    end

    function continuous(pieces::Int, t::Type{DistFixParam{T, F}}, d::ContinuousUnivariateDistribution) where {T, F}
        # d = Normal(mean, std)
        # @show t
        if t == DistInt
            # @show T, F
            whole_bits = 4
            point = 0   
        else
            whole_bits = T
            point = F
        end

        # @show whole_bits, point

        
        start = 0
        interval_sz = (2^whole_bits/pieces)
        # println(interval_sz)
        bits = Int(log2(interval_sz))
    
        areas = Vector(undef, pieces)
        total_area = 0
    
        end_pts = Vector(undef, pieces)
        for i=1:pieces
            p1 = start + (i-1)*interval_sz/2^point
            p2 = p1 + 1/2^point
            p3 = start + (i)*interval_sz/2^point
            p4 = p3 - 1/2^point
            # @show [p1, p2, p3, p4]
    
            pts = [cdf.(d, p2) - cdf.(d, p1), cdf.(d, p3) - cdf.(d, p4)]
            end_pts[i] = pts
    
            areas[i] = (pts[1] + pts[2])*2^(bits - 1)
            total_area += areas[i]
        end

        rel_prob = areas/total_area
        # @show rel_prob
        tria = triangle(bits, t)
        unif = uniform(bits, t)
        b = discrete2(rel_prob, DistInt)
        a = end_pts[pieces][1]/areas[pieces]
        l = a > 1/2^bits

        ans = t(dicecontext(), 2^whole_bits-1)
  
        # @show bits
        for i=pieces:-1:1
            if (areas[i] == 0)
                a = 0.0
            else
                a = end_pts[i][1]/areas[i]
            end
            l = a > 1/2^bits
            # @show bits
            # @show a
            # @show i
            ans = if prob_equals(b, i-1) 
                    (if l
                        t(dicecontext(), ((i)*2^bits - 1)) - 
                        # anyline(bits, 2/2^bits - a, t)
                        Dice.ifelse(flip(2 - a*2^bits), unif, tria)
                    else
                        t(dicecontext(), (i - 1)*2^bits) + 
                            # anyline(bits, a, t)
                            Dice.ifelse(flip(a*2^bits), unif, tria)
                    end)[1]
                else
                    ans
                end  
        end
        return ans
    end

    # mu = continuous(4, DistFixParam{4, 0}, Normal(8, 2))
    mu = continuous(32, DistFixParam{10, 0}, Normal(512, 131.282))
    # d = true
    # data1 = (continuous(128, DistFixParam{8, 4}, Normal(4, 2)) + mu)
    # d &= prob_equals(data1[1], DistFixParam{8, 4}(dicecontext(), 144)) & !data1[2]
    # data2 = (continuous(128, DistFixParam{8, 4}, Normal(4, 2)) + mu)
    # d &= prob_equals(data2[1], DistFixParam{8, 4}(dicecontext(), 144)) & !data2[2]
    # data3 = (continuous(128, DistFixParam{8, 4}, Normal(4, 2)) + mu)


    # d &= prob_equals(data3[1], DistFixParam{8, 4}(dicecontext(), 144)) & !data3[2]
    # Cond(mu, d)
    mu

    # a = triangle(3, DistInt).bits
    # if a[3] DistInt(4) else DistInt(a[1:2]) end
    # Cond(DistInt(a), d)
end



bdd = compile(code)
num_flips(bdd)
num_nodes(bdd)
a = (infer(code, :bdd))
a[70:100]
# @assert infer(code, :bdd) ≈ 0.5

bdd = compile(code)
num_flips(bdd)
num_nodes(bdd)
infer(code, :bdd)

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
    p = p[1:min(length(a), length(p))]
    a = a[1:min(length(a), length(p))]
    @show p
    @show length(a)
    kldivergence(p, map(a->a[2], a))
end

KL_div(a,10, 0, Normal(512, 131.282))