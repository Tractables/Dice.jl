using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir
using Distributions
using StatsBase
using Distances

`
This is the version of the algorithm with following features:
1. Equal linear pieces
2. Probability under each linear piece being invariant
3. The linear piece does not necessarily pass through start point or end point
`


function tug_of_war(p::Int)
    code = @dice begin

        function continuous(pieces::Int, t::Type{DistFixParam{T, F}}, d::ContinuousUnivariateDistribution) where {T, F}
            d = Truncated(d, 0, 2^(T-F))
            whole_bits = T
            point = F

            start = 0
            interval_sz = (2^whole_bits/pieces)

            @show interval_sz
            @show interval_sz * pieces/2^F

            while (cdf.(d, interval_sz*pieces/2^F) - cdf.(d, interval_sz*pieces/2^(F+1)) ≈ 0) & (interval_sz > 2)
                interval_sz /= 2
                @show interval_sz
            end

            @show interval_sz

            
            
            bits = Int(log2(interval_sz))
            areas = Vector(undef, pieces)
            trap_areas = Vector(undef, pieces)
            total_area = 0
        
            end_pts = Vector(undef, pieces)
            for i=1:pieces
                p1 = start + (i-1)*interval_sz/2^point
                p2 = p1 + 1/2^point
                p3 = start + (i)*interval_sz/2^point
                p4 = p3 - 1/2^point
        
                pts = [cdf.(d, p2) - cdf.(d, p1), cdf.(d, p3) - cdf.(d, p4)]
                end_pts[i] = pts
        
                trap_areas[i] = (pts[1] + pts[2])*2^(bits - 1)
                areas[i] = (cdf.(d, p3) - cdf.(d, p1))

                total_area += areas[i]
            end

            rel_prob = areas/total_area

            tria = triangle(dicecontext(), bits, t)
            unif = uniform(dicecontext(), bits, t)
            # @show rel_prob
            b = discrete2(dicecontext(), rel_prob, DistInt)

            ans = t(dicecontext(), (2^whole_bits-1)/2^F)
    
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
                ans = if prob_equals(b, i-1) 
                        (if l
                            # @show i*2^bits-1
                            t(dicecontext(), ((i)*2^bits - 1)/2^F) - 
                            anyline(dicecontext(), bits, 2/2^bits - a, t)
                            # Dice.ifelse(flip(2 - a*2^bits), unif, tria)
                        else
                            # @show (i-1)*2^bits
                            t(dicecontext(), (i - 1)*2^bits/2^F) + 
                                anyline(dicecontext(), bits, a, t)
                                # Dice.ifelse(flip(a*2^bits), unif, tria)
                        end)[1]
                    else
                        ans
                    end  
            end
            return ans
        end

        skillA = continuous(16, DistFixParam{6, 2}, Normal(5, 1))
        perfA1 = continuous(32, DistFixParam{6, 2}, Normal(5, 1)) + skillA
        perfA2 = continuous(32, DistFixParam{6, 2}, Normal(5, 1)) + skillA
        skillB = continuous(16, DistFixParam{6, 2}, Normal(5, 1))
        perfB1 = skillB + continuous(32, DistFixParam{6, 2}, Normal(5, 1))
        perfB2 = skillB + continuous(32, DistFixParam{6, 2}, Normal(5, 1))
        d = perfA1[1] > perfB1[1]
        Cond(perfA2[1] > perfB2[1], d)
        skillA
        perfA1[1]
    end
    code
end

a = tug_of_war(3)
bdd = compile(a)

num_flips(bdd)
num_nodes(bdd)
bdd = 1
p = infer(a, :bdd)