using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir
using Distributions

code = @dice begin
        
    function uniform(b::Int, t::Type)
        x = Vector(undef, b)
        for i = b:-1:1
            x[i] = flip(0.5)
        end
        return t(x)
    end

    function triangle(b::Int, t::Type)
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
        return t(x)
    end

    function discrete(p::Vector{Float64}, t::Type)
        mb = length(p)
        @assert sum(p) ≈ 1
        v = zeros(mb)
        sum_ = 1
        for i=1:mb
            # @show p[i], sum_
            # @show p[i] ≈ sum_
            if (p[i] >= sum_)
                v[i] = 1
                break
            else
                v[i] = p[i]/sum_
            end
            sum_ = sum_ - p[i]
            @show v[i]
            @assert v[i] >= 0
            @assert v[i] <= 1
        end

        ans = t(dicecontext(), mb-1)
        for i=mb-1:-1:1
            ans = if flip(v[i]) t(dicecontext(), i-1) else ans end
        end
        return ans
    end

    function discrete2(p::Vector{Float64}, t::Type)

        function recurse(p::Vector, i, s, e, prob::Vector)
            if (i == 0)
                flip(sum(prob[Int((s+e+1)/2):e])/sum(prob[s:e]))
            else
                (if p[length(p) - i + 1] recurse(p, i-1, Int((s+e+1)/2), e, prob) else recurse(p, i-1, s, Int((s+e-1)/2), prob) end)
            end
        end

        mb = length(p)
        add = Int(ceil(log2(mb)))
        p_proxy = vcat(p, zeros(2^add - mb))
        int_vector = []
        
        for i=1:add
            @show i
            a = recurse(int_vector, i-1, 1, 2^add, p_proxy)
            push!(int_vector, a)
        end
        t(reverse(int_vector))
    end

    function anyline(bits::Int, p::Float64, t::Type)
        # @show p*2^bits
        @assert p*2^bits >= 0
        @assert p*2^bits <= 1
        ans = Dice.ifelse(flip(p*2^bits), uniform(bits, t), triangle(bits, t))
        return ans
    end

    function continuous(pieces::Int, t::Type{DistFixParam{T, F}}, d::ContinuousUnivariateDistribution) where {T, F}

        a = [0.13, 0.58, 0.58, 0.13]
        b = [0, 4, 11, 15]
        f = [+, +, -, -]
        z = triangle(2, DistInt)
        # b2 = false
        # x2 = if b2 flip(0.5) else flip(0.16666666666666666) end
        # y2 = x2 || flip(0.8)
        # b1 = b2 || (!x2 && y2)
        # x1 = if b1 flip(0.5) else flip(0.0) end
        # y1 = x1 || flip(1)
        # b0 = b1 || (!x1 && y1)
        # z = (3 - DistInt([x2, x1]))[1]
        u = uniform(2, DistInt)#do i need to add bits for addition and all
        d = discrete2(a, DistInt)
        # d = discrete2([0.07393553696431762, 0.4260644630356824, 0.42606446303568235, 0.07393553696431762], DistInt)
        # final = if prob_equals(d, 0) 
        #             (0 + (if flip(a[1]) u else z end))[1] else
        #     (if prob_equals(d, 1) 
        #             (4 + (if flip(a[2]) u else z end))[1] else
        #     (if prob_equals(d, 2) 
        #             (11 - (if flip(a[3]) u else z end))[1] else
        #     (15 - (if flip(a[4]) u else z end))[1] end) end) end

        ans = (f[4](b[4],(if flip(a[4]) u else z end)))[1]

        for i=3:-1:1
            ans = if prob_equals(d, i-1)
                if a[i] > 1/2^2
                    ((i*2^2 - 1) - (if flip(a[i]) u else z end))[1]
                else 
                    ((i-1)*2^2 + (if flip(a[i]) u else z end))[1]
                end
                # (f[i](b[i], (if flip(a[i]) u else z end))[1])
            else
                ans
            end
        end


        return ans
    end

    # uniform(4, DistInt)
    # triangle(4, DistInt)
    # anyline(2, 0.1, DistInt)
    # discrete([0.1, 0.2, 0.3, 0.4], DistInt)
    # (continuous(4, DistFixParam{10, 7}, Normal(1, 0.25)) + continuous(4, DistFixParam{10, 7}, Normal(1, 0.25)))[1]
    # continuous(4, DistFixParam{4, 3}, Beta(1, 1))
    # continuous(4, DistFixParam{4, 2}, Exponential(1))
    continuous(16, DistFixParam{8, 0}, Normal(8, 2))
    # uniform(4, DistInt)
    # DistInt(dicecontext(), 255)
    skillA = continuous(16, DistFixParam{8, 4}, Normal(2, 0.5))

    perfA1 = continuous(16, DistFixParam{8, 4}, Normal(2, 0.5)) + skillA
    perfA2 = continuous(16, DistFixParam{8, 4}, Normal(2, 0.5)) + skillA
    skillB = continuous(16, DistFixParam{8, 4}, Normal(2, 0.5))

    perfB1 = continuous(16, DistFixParam{8, 4}, Normal(2, 0.5)) + skillB
    perfB2 = continuous(16, DistFixParam{8, 4}, Normal(2, 0.5)) + skillB

    d = (perfA2[1] > perfB2[1]) & !perfA2[2] & !perfB2[2]
    # Cond((perfA1[1] > perfB1[1]) & !perfA1[2] & !perfB1[2], d)
    skillA
end



bdd = compile(code)
a = (infer(code, :bdd))


num_flips(bdd)
num_nodes(bdd)