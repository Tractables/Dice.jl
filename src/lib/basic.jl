export uniform, triangle, discrete2, anyline

function uniform(mgr, b::Int, t::Type)
    x = Vector(undef, b)
    for i = b:-1:1
        x[i] = DistBool(mgr, 0.5)
    end
    return t(x)
end

function triangle(mgr, b::Int, t::Type)
    s = false
    n = 2^b
    x = Vector(undef, b)
    y = Vector(undef, b)
    for i = b:-1:1
        x[i] = Dice.ifelse(s, DistBool(mgr, 1/2), DistBool(mgr, (3n - 2)/ (4n-4)))
        y[i] = DistBool(mgr, (n-2)/(3n-2))
        s = s | (x[i] & !y[i])
        n = n/2
    end
    return t(x)
end

function discrete2(mgr, p::Vector{Float64}, t::Type)

    function recurse(p::Vector, i, s, e, prob::Vector)
        if (i == 0)
            DistBool(mgr, sum(prob[Int((s+e+1)/2):e])/sum(prob[s:e]))
        else
            (Dice.ifelse(p[length(p) - i + 1], recurse(p, i-1, Int((s+e+1)/2), e, prob), recurse(p, i-1, s, Int((s+e-1)/2), prob)))
            # if p[length(p) - i + 1] recurse(p, i-1, Int((s+e+1)/2), e, prob) else recurse(p, i-1, s, Int((s+e-1)/2), prob) end
            
        end
    end

    mb = length(p)
    add = Int(ceil(log2(mb)))
    p_proxy = vcat(p, zeros(2^add - mb))
    int_vector = []
    
    for i=1:add
        # @show i
        a = recurse(int_vector, i-1, 1, 2^add, p_proxy)
        push!(int_vector, a)
    end
    if add == 0 t(mgr, 0) else t(reverse(int_vector)) end
end

function anyline(mgr, bits::Int, p::Float64, t::Type)
    # @show p*2^bits
    @assert p*2^bits >= 0
    @assert p*2^bits <= 1
    ans = Dice.ifelse(DistBool(mgr, p*2^bits), uniform(mgr, bits, t), triangle(mgr, bits, t))
    return ans
end

