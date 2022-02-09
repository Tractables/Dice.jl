using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir
using Distributions

code = @dice begin
    # triangle distribution

    function triangle(b::Int)
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
        return ProbInt(x)
    end

    function uniform(b::Int) # b is the bits for uniform, w is the bitwidth
        x = Vector(undef, b)
        for i = b:-1:1
            x[i] = flip(0.5)
        end
        return ProbInt(x)
    end

    function discrete(p::Vector{Float64})
        mb = length(p)
        v = Vector(undef, mb)
        sum = 1
        for i=1:mb
            v[i] = p[i]/sum
            sum = sum - p[i]
        end

        # println(v)
        ans = ProbInt(dicecontext(), mb-1)
        for i=mb-1:-1:1
            ans = if flip(v[i]) ProbInt(dicecontext(), i-1) else ans end
        end
        return ans
    end

    function anyline(bits::Int, p::Float64)
        ans = Dice.ifelse(flip(p*2^bits), add_bits(uniform(bits), 3), add_bits(triangle(bits), 3))
        return ans
    end

    function gaussian(bits::Int, pieces::Int)
        d = Normal()
        start = quantile.(Normal(), 0.001)
        interval_sz = 2*abs(start)/pieces
    
        areas = Vector(undef, pieces)
        total_area = 0
    
        end_pts = Vector(undef, pieces)
        for i=1:pieces
            p1 = start + (i-1)*interval_sz
            p2 = p1 + interval_sz/2^bits
            p3 = start + (i)*interval_sz
            p4 = p3 - interval_sz/2^bits
    
            pts = [cdf.(d, p2) - cdf.(d, p1), cdf.(d, p3) - cdf.(d, p4)]
            end_pts[i] = pts
    
            areas[i] = (pts[1] + pts[2])*2^(bits - 1)
            total_area += areas[i]
        end

        # println(total_area)
    
        rel_prob = areas/total_area
    
        b = discrete(rel_prob)
        a = end_pts[pieces][1]/areas[pieces]
        l = a > 1/2^bits
        ans =  (if l
                    2^bits - 1 + (pieces - 1)*2^bits - add_bits(anyline(bits, 2/2^bits - a), 3)
                else
                    (pieces - 1)*2^bits + add_bits(anyline(bits, a), 3)
                end)[1]

        for i=pieces-1:-1:1
            a = end_pts[i][1]/areas[i]
            l = a > 1/2^bits
            ans = if prob_equals(b, i-1) 
                    (if l
                        (2^bits - 1 + (i - 1)*2^bits - anyline(bits, 2/2^bits - a))
                    else
                        (i - 1)*2^bits + 
                            anyline(bits, a)
                    end)[1]
                else
                    ans
                end  
        end
        return ans
    end
    # println(max_bits(add_bits(anyline(2, 0.1), 3)))
    # println(max_bits(gaussian(2, 4)))
    g = gaussian(1, 108)
    rep = (g > 107) & (143 > g)
    rep
end



bdd = compile(code)
num_flips(bdd)
num_nodes(bdd)
println(infer(code, :bdd))
@assert infer(code, :bdd) ≈ 0.5

bdd = compile(code)
num_flips(bdd)
num_nodes(bdd)
infer(code, :bdd)