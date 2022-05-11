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


function single_gaussian(p::Int, binbits::Int)
    code = @dice begin

        function continuous(pieces::Int, t::Type{DistFixParam{T, F}}, d::ContinuousUnivariateDistribution) where {T, F}
            d = Truncated(d, 0, 2^(T-F))
            whole_bits = T
            point = F

            start = 0
            interval_sz = (2^whole_bits/pieces)

            while cdf(d, pieces*interval_sz/2^point) ≈ cdf(d, (pieces-1)*interval_sz/2^point)
                #Need to come up with a better way for this condition, specifying epsilon
                if interval_sz == 2
                    break
                else
                    interval_sz = interval_sz/2
                end
            end
            # @show interval_sz
            
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
                # @show p3, p1, areas[i]

                total_area += areas[i]
            end

            rel_prob = areas/total_area
            # @show areas
            # @show end_pts

            tria = triangle(dicecontext(), bits, t)
            # @show bits
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
            # return Dice.ifelse(flip(0.5), unif, tria)
            return ans
        end

        alice = continuous(p, DistFixParam{binbits + 4, binbits}, Normal(5, 1))
        bob = continuous(p, DistFixParam{binbits + 4, binbits}, Normal(5, 1))
        e = DistFixParam{binbits + 4, binbits}(dicecontext(), 2.0)
        obs = true
        obs &= (if flip(1/3) 
                    ((alice - e)[1]) else alice end) > (if flip(1/3) 
                                                        (bob - e)[1] else bob end)
        obs &= (if flip(1/3) 
        ((bob - e)[1]) else bob end) > (if flip(1/3) 
                                            (alice - e)[1] else alice end)
        obs &= (if flip(1/3) 
        ((alice - e)[1]) else alice end) > (if flip(1/3) 
                                            (bob - e)[1] else bob end)
        obs &= (if flip(1/3) 
        ((bob - e)[1]) else bob end) > (if flip(1/3) 
                                        (alice - e)[1] else alice end)

        Cond((if flip(1/3) 
        ((alice - e)[1]) else alice end) > (if flip(1/3) 
                                            (bob - e)[1] else bob end), obs)
        
        # (alice-e)[1]
        alice
        
    end
    code
end


code = single_gaussian(1, 1)
bdd = compile(code)
a = @benchmark infer(single_gaussian(1, 1), :bdd)
d = KL_div(b, 10, 0, Gamma(1, 512))

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

for i = 1:2
    for j = 1:2
        a = @benchmark infer(single_gaussian($i, $j), :bdd)
        println(median(a))
    end
end