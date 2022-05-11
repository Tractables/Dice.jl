using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir
using Distributions
using StatsBase
using Distances

code = @dice begin
    function continuous(pieces::Int, t::Type{DistFixParam{T, F}}, d::ContinuousUnivariateDistribution) where {T, F}
        d = Truncated(d, 0, 2^(T-F))
        whole_bits = T
        point = F

        start = 0
        interval_sz = (2^whole_bits/pieces)

        while (cdf.(d, interval_sz*pieces/2^F) - cdf.(d, interval_sz*pieces/2^(F+1)) ≈ 0) & (interval_sz > 2)
            interval_sz /= 2
        end
        
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
    
            # areas[i] = 
            # @show areas[i]
            trap_areas[i] = (pts[1] + pts[2])*2^(bits - 1)
            areas[i] = (cdf.(d, p3) - cdf.(d, p1))

            total_area += areas[i]
        end

        rel_prob = areas/total_area
        @show areas
        @show end_pts

        tria = triangle(dicecontext(), bits, t)
        unif = uniform(dicecontext(), bits, t)
        @show rel_prob
        b = discrete2(dicecontext(), rel_prob, DistInt)

        @show t, (2^whole_bits - 1)/2^F
        ans = t(dicecontext(), Float64((2^whole_bits-1)/2^F))

        for i=pieces:-1:1
            if (trap_areas[i] == 0)
                a = 0.0
            else
                a = end_pts[i][1]/trap_areas[i]
            end
            @show i, a
            @show bits
            @assert 2 - a*2^bits >= 0
            l = a > 1/2^bits
            
            # @show a
            # @show i
            # @show a*2^bits
            ans = if prob_equals(b, i-1) 
                    (if l
                        # @show i*2^bits-1
                        t(dicecontext(), ((i)*2^bits - 1)/2^F) - 
                        # anyline(dicecontext(), bits, 2/2^bits - a, t)
                        Dice.ifelse(flip(2 - a*2^bits), unif, tria)
                    else
                        # @show (i-1)*2^bits
                        t(dicecontext(), (i - 1)*2^bits/2^F) + 
                            # anyline(dicecontext(), bits, a, t)
                            Dice.ifelse(flip(a*2^bits), unif, tria)
                    end)[1]
                else
                    ans
                end  
        end
        return ans
    end

    d1 = continuous(8, DistFixParam{13, 9}, 4*Beta(8, 2))
    d2 = continuous(8, DistFixParam{13, 9}, 10*Beta(5, 5))
    
    gpa1 = if flip(0.95) d1 else 
                if flip(0.15) DistFixParam{13, 9}(dicecontext(), 0.0) else
                    DistFixParam{13, 9}(dicecontext(), 4.0)
                end
            end

    gpa2 = if flip(0.99) d2 else 
        if flip(0.1) DistFixParam{13, 9}(dicecontext(), 0.0) else
            DistFixParam{13, 9}(dicecontext(), 10.0)
        end
    end

    n = flip(0.25)
    final = if n gpa1 else gpa2 end
    o = prob_equals(final, DistFixParam{13, 9}(dicecontext(), 3.0))
    Cond(n, o)
    # gpa2
    # d2
    # d1 * DistFixParam{10, 0}(dicecontext(), 2)

    # d1 = discrete2(dicecontext(), [0.1, 0.2, 0.3, 0.4, 0, 0, 0, 0], DistInt)

    # DistFixParam{10, 4}(dicecontext(), 4.33)

end

# BDD analysis
# bdd = compile(code)
# num_flips(bdd), num_nodes(bdd)
# infer(code, :bdd)

function execute(code)
    @time infer(code, :bdd)
end

execute(code)