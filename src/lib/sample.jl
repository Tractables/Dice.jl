# Sample from discrete distributions
export uniform_int, discrete, discrete_int

function uniform_int(domain::AbstractVector{Int})
    p = zeros(maximum(domain) + 1)
    for x in domain
        p[x + 1] = 1/length(domain)
    end
    discrete_int(p)
end

function discrete_int(p::Vector{Float64})
    mb = length(p)
    v = Vector(undef, mb)
    sum = 1
    for i=1:mb
        v[i] = p[i]/sum
        sum = sum - p[i]
    end
    ans = DistInt(mb-1)
    for i=mb-1:-1:1
        ans = Dice.ifelse(flip(v[i]), DistInt(i-1), ans)
    end
    return ans
end

function discrete(dist_p_tups)
    dist_p_tups = collect(dist_p_tups)
    v = Dict()
    sum = 1.
    for (val, weight) in dist_p_tups
        v[val] = weight/sum
        sum -= weight
    end

    ans = last(dist_p_tups)[1]
    for i = (length(dist_p_tups) - 1):-1:1
        (val, weight) = dist_p_tups[i]
        ans = @dice_ite if flip(v[val]) val else ans end
    end
    return ans
end

# TODO: add bitwise holtzen
