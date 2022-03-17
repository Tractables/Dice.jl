using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir
using Distributions
using StatsBase
using Distances

function single_gaussian(p::Int, T, d, flag::Bool)
    code = @dice begin

        function continuous(pieces::Int, t::Type{DistFixParam{T, F}}, d::ContinuousUnivariateDistribution, flag::Bool) where {T, F}
            d = Truncated(d, 0, 2^(T-F))
            whole_bits = T
            point = F

            start = 0
            interval_sz = (2^whole_bits/pieces)
            
            bits = Int(log2(interval_sz))
            areas = Vector(undef, pieces)
            total_area = 0
        
            end_pts = Vector(undef, pieces)
            for i=1:pieces
                p1 = start
                p2 = p1 + 1/2^point
                p3 = start + interval_sz/2^point
                p4 = p3 - 1/2^point
        
                pts = [cdf.(d, p2) - cdf.(d, p1), cdf.(d, p3) - cdf.(d, p4)]
                end_pts[i] = pts
        
                areas[i] = (pts[1] + pts[2])*interval_sz/2
                total_area += areas[i]
                start = start + interval_sz
            end

            rel_prob = areas/total_area

            tria = triangle(dicecontext(), bits, t)
            unif = uniform(dicecontext(), bits, t)
            b = discrete2(dicecontext(), rel_prob, DistInt)

            ans = t(dicecontext(), 0)
    
            for i=pieces:-1:1
                if (areas[i] == 0)
                    a = 0.0
                else
                    a = end_pts[i][1]/areas[i]
                end
                l = a > 1/2^bits

                ans = if prob_equals(b, i-1) 
                        if flag
                            (if l
                                t(dicecontext(), ((i)*2^bits - 1)) - 
                                # anyline(dicecontext(), bits, 2/2^bits - a, t)
                                Dice.ifelse(flip(2 - a*2^bits), uniform(dicecontext(), bits, t), tria)
                            else
                                t(dicecontext(), (i - 1)*2^bits) + 
                                    # anyline(dicecontext(), bits, a, t)
                                    Dice.ifelse(flip(a*2^bits), uniform(dicecontext(), bits, t), tria)
                            end)[1]
                        else
                            (if l
                                t(dicecontext(), ((i)*2^bits - 1)) - 
                                # anyline(bits, 2/2^bits - a, t)
                                
                                Dice.ifelse(flip(2 - a*2^bits), unif, tria)
                            else
                                t(dicecontext(), (i - 1)*2^bits) + 
                                    # anyline(bits, a, t)
                                    
                                    Dice.ifelse(flip(a*2^bits), unif, tria)
                            end)[1]
                        end
                    else
                        ans
                    end  
            end
            return ans
        end

        d = continuous(p, DistFixParam{3, 0}, d, flag)
        d
        
    end
    code
end



function kl_divergence(p, q)
    @assert sum(p) ≈ 1.0
    @assert sum(q) ≈ 1.0
    ans = 0
    for i=1:length(p)
        if p[i] > 0
            ans += p[i] *(log(p[i]) - log(q[i]))
        end
    end
    ans
end


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
    # kl_divergence(p, map(a->a[2], a))
    @show p .- map(a->a[2], a)
    chebyshev(p, map(a->a[2], a))
end

function cmp_kl(p, T, F, d)
    code1 = single_gaussian(p, DistFixParam{T, F}, d, false)
    b1 = infer(code1, :bdd)
    @show b1
    code2 = single_gaussian(p, DistFixParam{T, F}, d, true)
    b2 = infer(code2, :bdd)
    @show b2
    ans = KL_div(b1, T, F, d), KL_div(b2, T, F, d)
    ans
end

cmp_kl(4, 3, 0, Normal(4, 1))
code = single_gaussian(4, DistFixParam{3, 0}, Normal(4, 1), false)
b = infer(code, :bdd)
