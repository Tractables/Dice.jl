using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir
using Distributions

code = @dice begin
        
    function uniform(b::Int, point::Int)
        x = Vector(undef, b)
        for i = b:-1:1
            x[i] = flip(0.5)
        end
        return DistFix(x, point)
    end

    function triangle(b::Int, point::Int)
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
        return DistFix(x, point)
    end

    function discrete(p::Vector{Float64}, point)
        mb = length(p)
        # v = Vector(undef, mb)
        v = zeros(mb)
        sum = 1
        for i=1:mb
            if (p[i] ≈ sum)
                v[i] = 1
                break
            else
                v[i] = p[i]/sum
            end
            sum = sum - p[i]
            @assert v[i] >= 0
            @assert v[i] <= 1
        end

        ans = DistFix(dicecontext(), mb-1, point)
        for i=mb-1:-1:1
            ans = if flip(v[i]) DistFix(dicecontext(), i-1, point) else ans end
        end
        return ans
    end


    function discrete(p::Vector{Float64})
        mb = length(p)
        # v = Vector(undef, mb)
        v = zeros(mb)
        sum = 1
        for i=1:mb
            if (p[i] >= sum)
                v[i] = 1
                break
            else
                v[i] = p[i]/sum
            end
            sum = sum - p[i]
            # @show [i, v[i]]
            @assert v[i] >= 0
            @assert v[i] <= 1
        end

        ans = DistInt(dicecontext(), mb-1)
        for i=mb-1:-1:1
            ans = if flip(v[i]) DistInt(dicecontext(), i-1) else ans end
        end
        return ans
    end

    function anyline(bits::Int, p::Float64, point::Int)
        @show p*2^bits
        @assert p*2^bits >= 0
        @assert p*2^bits <= 1
        ans = Dice.ifelse(flip(p*2^bits), uniform(bits, point), triangle(bits, point))
        return ans
    end

    function continuous(whole_bits::Int, pieces::Int, point::Int, d::ContinuousUnivariateDistribution)
        # d = Normal(mean, std)
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
        # @show rel_prob
        b = discrete(rel_prob)
        a = end_pts[pieces][1]/areas[pieces]
        l = a > 1/2^bits

        ans = DistFix(dicecontext(), 2^whole_bits, point)
  
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
                        DistFix(dicecontext(), ((i)*2^bits - 1), point) - anyline(bits, 2/2^bits - a, point)
                    else
                        DistFix(dicecontext(), (i - 1)*2^bits, point) + 
                            anyline(bits, a, point)
                    end)[1]
                else
                    ans
                end  
        end
        return ans
    end

    mu = continuous(5, 16, 2, Exponential(1))
    d = prob_equals((continuous(5, 16, 2, Normal(0, 1)) + mu)[1], DistFix(dicecontext(), 20, 2)) # == 5
    # d &= prob_equals((gaussian(6, 8, 8.0, 1.0) + mu)[1], 18)
    # ((n1 + n2)[1])
    # CondBool(10 > mu && mu > 7, d)
    # Cond(mu, d)
    mu
end



bdd = compile(code)
(infer(code, :bdd))
# @assert infer(code, :bdd) ≈ 0.5

bdd = compile(code)
num_flips(bdd)
num_nodes(bdd)
infer(code, :bdd)