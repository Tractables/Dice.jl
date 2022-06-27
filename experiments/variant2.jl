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


function single_gaussian(p::Int)
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
            @show areas
            @show end_pts

            tria = triangle(dicecontext(), bits, t)
            unif = uniform(dicecontext(), bits, t)
            @show rel_prob
            b = discrete2(dicecontext(), rel_prob, DistInt)

            ans = t(dicecontext(), Float64(2^whole_bits-1))
    
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
                            t(dicecontext(), Float64((i)*2^bits - 1)) - 
                            # anyline(dicecontext(), bits, 2/2^bits - a, t)
                            Dice.ifelse(flip(2 - a*2^bits), unif, tria)
                        else
                            # @show (i-1)*2^bits
                            t(dicecontext(), Float64((i - 1)*2^bits)) + 
                                # anyline(dicecontext(), bits, a, t)
                                Dice.ifelse(flip(a*2^bits), unif, tria)
                        end)[1]
                    else
                        ans
                    end  
            end
            return ans
        end

        d = continuous(p, DistFixParam{10, 0}, Normal(200, 50))
        d
    end
    code
end


code = single_gaussian(64)
bdd = compile(code)
a = infer(code, :bdd)
d = KL_div(b, 10, 0, Normal(512, 512/3.09))

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
    
    p = p[1:length(a)]
    # @show sum(map(a->a[2], a))
    # @show p
    # @show length(a)
    ans = Vector(undef, length(a))
    for i=1:length(a)
        ans[i] = p[i] * (log(p[i]) - log(a[i][2]))
    end
    plot(map(a -> a[2], a), ans)
        
    kldivergence(p, map(a->a[2], a))
    # ans
    p
    # chebyshev(p, map(a->a[2], a))
end

count = 1
data = Vector{Float64}(undef, 0)
i = 0
equal = Vector(undef, 10)
while count < 1024
    code = single_gaussian(count)
    bdd = compile(code)
    a = infer(code, :bdd)
    # @show a
    i = i+1
    equal[i] = a
    k = KL_div(a, 10, 0, Normal(512, 512/3.09))
    @show count, k, num_flips(bdd), num_nodes(bdd)
    append!(data, log2(k))
    count = count*2
end