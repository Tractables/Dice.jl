using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir
using Distributions
using StatsBase
using Distances

function single_gaussian(p::Int)
    code = @dice begin

        function continuous(pieces::Int, t::Type{DistFixParam{T, F}}, d::ContinuousUnivariateDistribution) where {T, F}
            d = Truncated(d, 0, 2^(T-F))
            # @show t
            whole_bits = T
            point = F

            # @show whole_bits, point
            start = 0
            interval_sz = (2^whole_bits/pieces)
            
            bits = Int(log2(interval_sz))
            # @show bits
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
            # @show areas
            rel_prob = areas/total_area
            @show total_area
            # @show rel_prob
            tria = triangle(dicecontext(), bits, t)
            unif = uniform(dicecontext(), bits, t)
            b = discrete2(dicecontext(), rel_prob, DistInt)

            ans = t(dicecontext(), 2^whole_bits-1)
    
            # @show bits
            for i=pieces:-1:1
                if (areas[i] == 0)
                    a = 0.0
                else
                    a = end_pts[i][1]/areas[i]
                end
                # @show a
                l = a > 1/2^bits
                # @show bits
                # @show a
                # @show i
                # @show a*2^bits
                ans = if prob_equals(b, i-1) 
                        (if l
                            # @show i*2^bits-1
                            t(dicecontext(), ((i)*2^bits - 1)) - 
                            # anyline(dicecontext(), bits, 2/2^bits - a, t)
                            Dice.ifelse(flip(2 - a*2^bits), unif, tria)
                        else
                            # @show (i-1)*2^bits
                            t(dicecontext(), (i - 1)*2^bits) + 
                                # anyline(dicecontext(), bits, a, t)
                                Dice.ifelse(flip(a*2^bits), unif, tria)
                        end)[1]
                    else
                        ans
                    end  
            end
            return ans
        end

        # skillA = continuous(8, DistFixParam{8, 0}, Normal(50, 10))

        # perfA1 = continuous(8, DistFixParam{8, 0}, Normal(50, 15)) + skillA
        # # perfA2 = continuous(8, DistFixParam{8, 0}, Normal(50, 15)) + skillA
        # skillB = continuous(8, DistFixParam{8, 0}, Normal(50, 10))
        # perfB1 = continuous(8, DistFixParam{8, 0}, Normal(50, 15)) + skillB

        # perfB2 = continuous(8, DistFixParam{8, 0}, Normal(50, 15)) + skillB
        # # # perfB2 = continuous(16, DistFixParam{8, 4}, Normal(2, 0.5)) + skillB

        # # d = (perfA2[1] > perfB2[1]) & !perfA2[2] & !perfB2[2]
        # # Cond((perfA1[1] > perfB1[1]) & !perfA1[2] & !perfB1[2], d)
        # # # (perfA2[1] > perfB2[1]) & !perfA2[2] & !perfB2[2]
        # # # d
        # skillA
        # (perfB1[1] > perfA1[1]) & !perfA1[2] & !perfB1[2]
        # perfA1[1]
        d = continuous(p, DistFixParam{10, 0}, Normal(512, 512/3.09))
        d
    end
    code
end


code = single_gaussian(16)
bdd = compile(code)
b = infer(code, :bdd)
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
    # p
    # chebyshev(p, map(a->a[2], a))
end

count = 1
data2 = Vector{Float64}(undef, 0)
i = 0
equal = Vector(undef, 10)
while count < 1024
    code = single_gaussian(count)
    bdd = compile(code)
    a = infer(code, :bdd)
    # @show a
    i = i+1
    equal[i] = a
    k = KL_div(a, 10, 0, Normal(512, 82.84789644012946*2))
    @show count, k, num_flips(bdd), num_nodes(bdd)
    append!(data2, log2(k))
    count = count*2
end