using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir
using Distributions
using StatsBase
using Distances

```
This is the version of the algorithm with following features:
1. Unequal linear pieces
2. Probability under each linear piece being invariant
3. The linear piece pass through the initial point
```

function single_gaussian(p::Int)
    code = @dice begin
        
        function max_index_not1(prob::Vector, piece::Vector)
            max = 0
            for i=1:length(prob)
                if piece[i] == 1
                    continue
                else
                    if (max == 0)
                        max = i
                    else
                        if prob[i] > prob[max]
                            max = i
                        else
                            max = max
                        end
                    end
                end
            end
            # @assert max != 0
            max
        end 


        function piece_dist(pieces::Int, t::Type{DistFixParam{T, F}}, d::ContinuousUnivariateDistribution) where {T, F}
            # d = Normal(mean, std)
            @assert pieces <= 2^(T-1)
            d = Truncated(d, 0, 2^(T-F))
            piece_size = [T]
            # @show piece_size
            while (length(piece_size) < pieces)
                prob = []
                lower = 0
                upper = 0
                for i = 1:length(piece_size)
                    # @show lower
                    upper = lower + 2^piece_size[i]/2^(F)
                    # @show upper
                    # @show cdf(d, upper) - cdf(d, lower)
                    append!(prob, cdf(d, upper) - cdf(d, lower))
                    lower = upper
                end
                # @show prob
                lastindex = length(prob)
                for j=length(prob):-1:1
                    if prob[j] ≈ 0
                        lastindex -=1
                    else
                        break
                    end
                end


                a = max_index_not1(prob[1:lastindex], piece_size[1:lastindex])
                if a == 0
                    break
                    # @show prob
                else
                    
                    # @show a
                    piece_size = vcat(piece_size[1:a-1], [piece_size[a]-1, piece_size[a]-1], piece_size[a+1: lastindex])
                    # @show piece_size
                    # @show prob
                end
                
            end
            # @show length(piece_size)
            # @show prob
            # @show piece_size
            piece_size
        end

        function continuous(pieces::Int, t::Type{DistFixParam{T, F}}, d_proxy::ContinuousUnivariateDistribution) where {T, F}
            whole_bits = T
            point = F
            d = Truncated(d_proxy, 0, 2^(T - F))

            start = 0
            interval_sz = piece_dist(pieces, t, d)
            # @show interval_sz
            pieces = length(interval_sz)
            
            areas = Vector{Float64}(undef, pieces)
            total_area = 0
        
            end_pts = Vector(undef, pieces)
            for i=1:pieces
                p1 = start
                p2 = p1 + 1/2^point
                p3 = start + 2^interval_sz[i]/2^point
                p4 = p3 - 1/2^point
                pts = [cdf.(d, p2) - cdf.(d, p1), cdf.(d, p3) - cdf.(d, p4)]
                @show (p1, p2, p4, p3)
                end_pts[i] = pts
        
                # areas[i] = (pts[1] + pts[2])*2^(interval_sz[i] - 1)
                areas[i] = cdf.(d, p3) - cdf.(d, p1)
                total_area += areas[i]
                start = start + 2^interval_sz[i]/2^point
            end

            # @show end_pts
            # @show areas
            rel_prob = areas/total_area
            # @show sum(rel_prob)
            # @show total_area
            # @show rel_prob
            @show interval_sz
            
            b = discrete2(dicecontext(), rel_prob, DistInt)
            flip_vector = Vector(undef, pieces)
            

            a = end_pts[pieces][1]/areas[pieces]
            ans = t(dicecontext(), 2^whole_bits-1)
    
            # @show bits
            position = 0
            for i=1:length(interval_sz)
                position += 2^interval_sz[i]
            end

            for i=pieces:-1:1
                if (areas[i] == 0)
                    a = 0.0

                else
                    if end_pts[i][1] > end_pts[i][2]
                        a = end_pts[i][2]/areas[i]
                    else
                        a = end_pts[i][1]/areas[i]
                    end

                    # if end_pts[i][1] > end_pts[i][2]
                    #     a = end_pts[i][2] * 2/ (2^interval_sz[i] * sum(end_pts[i]))
                    # else
                    #     a = end_pts[i][1] * 2/ (2^interval_sz[i] * sum(end_pts[i]))
                    # end
                end

                @show end_pts[i]
                l = end_pts[i][1] > end_pts[i][2]

                position -= 2^interval_sz[i]
                ans = 
                    if prob_equals(b, i-1) 
                        (if l
                            t(dicecontext(), position + 2^interval_sz[i] - 1) - 
                            anyline(dicecontext(), interval_sz[i], a, t)
                            # Dice.ifelse(flip(2 - a*2^interval_sz[i]), t(unif[1:interval_sz[i]]), triangle(interval_sz[i], t))
                        else
                            t(dicecontext(), position) + 
                                anyline(dicecontext(), interval_sz[i], a, t)
                                # Dice.ifelse(flip(a*2^interval_sz[i]), t(unif[1:interval_sz[i]]), triangle(interval_sz[i], t))
                        end)[1]
                    else
                        ans
                    end  
            end
            @show interval_sz
            return ans
        end
        d = continuous(p, DistFixParam{10, 0}, Normal(512, 512/3.09))
        # anyline(dicecontext(), 2, 0.1, DistInt)
    end
    code
    
end

code = single_gaussian(16)
bdd = compile(code)
a = infer(code, :bdd)
d = KL_div(a, 10, 0, Normal(512, 512/3.09))
num_flips(bdd)
num_nodes(bdd)
k = KL_div(a, 10, 0, Normal(512, 82.84789644012946*2))
    @show count, k, num_flips(bdd), num_nodes(bdd)
    count = count*2
totalvariation(p, a)


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
    # @show length(p)
    # @show length(a)
    p = p[1:length(a)]
    # @show sum(map(a->a[2], a))
    # @show p
    # @show length(a)
    ans = Vector(undef, length(a))
    for i=1:length(a)
        ans[i] = p[i]*(log(p[i]) - log(a[i][2]))
    end
    # ans
    
    kldivergence(p, map(a->a[2], a))
    # chebyshev(p, map(a->a[2], a))
end

count = 1
data = Vector{Float64}(undef, 0)
unequal = Vector(undef, 10)
i = 0
while count < 1024
    code = single_gaussian(count)
    bdd = compile(code)
    a = infer(code, :bdd)
    i = i+1
    unequal[i] = a
    # @show a
    k = KL_div(a, 10, 0, Normal(512, 82.84789644012946*2))
    @show count, k, num_flips(bdd), num_nodes(bdd)
    append!(data, log2(k))
    count = count*2
end


