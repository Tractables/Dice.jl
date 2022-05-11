using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir
using Distributions

code = @dice begin

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
            @show [p1, p2, p3, p4]
    
            pts = [cdf.(d, p2) - cdf.(d, p1), cdf.(d, p3) - cdf.(d, p4)]
            end_pts[i] = pts
    
            areas[i] = (pts[1] + pts[2])*2^(bits - 1)
            total_area += areas[i]
        end
        @show areas
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

    skillA = continuous(16, DistFixParam{8, 0}, Normal(2, 0.5))

    perfA1 = continuous(16, DistFixParam{8, 4}, Normal(2, 0.5)) + skillA
    # perfA2 = continuous(16, DistFixParam{8, 4}, Normal(2, 0.5)) + skillA
    skillB = continuous(16, DistFixParam{8, 4}, Normal(2, 0.5))

    perfB1 = continuous(16, DistFixParam{8, 4}, Normal(2, 0.5)) + skillB
    perfB2 = continuous(16, DistFixParam{8, 4}, Normal(2, 0.5)) + skillB

    d = (perfA2[1] > perfB2[1]) & !perfA2[2] & !perfB2[2]
    Cond((perfA1[1] > perfB1[1]) & !perfA1[2] & !perfB1[2], d)
    (perfA2[1] > perfB2[1]) & !perfA2[2] & !perfB2[2]
    d
    skillA
    perfB1[1] > perfA1[1]
    # continuous(8, DistFixParam{4, 0}, Normal(512, 82.84789644012946*2))
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