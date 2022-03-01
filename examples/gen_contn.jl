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
        @show sum(p)
        @assert sum(p) ≈ 1
        v = zeros(mb)
        sum_ = 1
        for i=1:mb
            @show p[i], sum_
            @show p[i] ≈ sum_
            if (p[i] > sum_)
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

    function anyline(bits::Int, p::Float64, t::Type)
        @show p*2^bits
        @assert p*2^bits >= 0
        @assert p*2^bits <= 1
        ans = Dice.ifelse(flip(p*2^bits), uniform(bits, t), triangle(bits, t))
        return ans
    end

    function continuous(pieces::Int, t::Type{DistFixParam{T, F}}, d::ContinuousUnivariateDistribution) where {T, F}
        # d = Normal(mean, std)
        @show t
        if t == DistInt
            # @show T, F
            whole_bits = 4
            point = 0   
        else
            whole_bits = T
            point = F
        end

        @show whole_bits, point

        
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
            @show [p1, p2, p3, p4]
    
            pts = [cdf.(d, p2) - cdf.(d, p1), cdf.(d, p3) - cdf.(d, p4)]
            end_pts[i] = pts
    
            areas[i] = (pts[1] + pts[2])*2^(bits - 1)
            total_area += areas[i]
        end

        rel_prob = areas/total_area
        @show rel_prob
        b = discrete(rel_prob, DistInt)
        a = end_pts[pieces][1]/areas[pieces]
        l = a > 1/2^bits

        ans = t(dicecontext(), 2^whole_bits)
  
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
                        t(dicecontext(), ((i)*2^bits - 1)) - anyline(bits, 2/2^bits - a, t)
                    else
                        t(dicecontext(), (i - 1)*2^bits) + 
                            anyline(bits, a, t)
                    end)[1]
                else
                    ans
                end  
        end
        return ans
    end

    # discrete([0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.3], DistFixParam{3, 2})
    # triangle(3, DistFixParam{3, 0})
    # anyline(2, 0.1, DistFixParam{2, 1})
    continuous(8, DistFixParam{4, 3}, Normal(1, 0.125))
end



bdd = compile(code)
(infer(code, :bdd))
# @assert infer(code, :bdd) ≈ 0.5

bdd = compile(code)
num_flips(bdd)
num_nodes(bdd)
infer(code, :bdd)