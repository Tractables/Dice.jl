# Sample from discrete distributions
export uniform_int, discrete, discrete_sbk, discrete_int, discrete_int_sbk

# TODO: add more efficient uniform implementation for contiguous ranges
function uniform_int(domain::AbstractVector{Int})
    p = zeros(maximum(domain) + 1)
    for x in domain
        p[x + 1] = 1/length(domain)
    end
    discrete_int(p)
end

function discrete_int(p)
    p = collect(p)
    while !ispow2(length(p))
        push!(p, 0.)
    end

    prefix_sums = accumulate(+, p)
    # Slightly looser approximate equality requirement as we use discrete_int
    # for some .bif files converted to Dice.jl programs.
    @assert isapprox(last(prefix_sums), 1, atol=1e-5) "Probabilities must sum to 1"

    function helper(i, j)
        if i == j
            DistInt(i - 1)
        else
            first_half_end = (i + j - 1) ÷ 2
            first_half_p = prefix_sums[first_half_end] - prefix_sums[i] + p[i]
            total_p = prefix_sums[j] - prefix_sums[i] + p[i]
            ifelse(flip(first_half_p/total_p),
                helper(i, first_half_end),
                helper(first_half_end+1, j))
        end
    end
    helper(1, length(p))
end

function discrete_int_sbk(p::AbstractVector{Float64})
    @assert sum(p) ≈ 1 "Probabilities must sum to 1"
    mb = length(p)
    v = Vector(undef, mb)
    p_sum = 1
    for i=1:mb
        v[i] = p[i]/p_sum
        p_sum = p_sum - p[i]
    end
    ans = DistInt(mb-1)
    for i=mb-1:-1:1
        ans = Dice.ifelse(flip(v[i]), DistInt(i-1), ans)
    end
    return ans
end

function discrete(dist_p_tups)
    dist_p_tups = collect(dist_p_tups)
    @assert sum(p for (d, p) in dist_p_tups) ≈ 1 "Probabilities must sum to 1"

    # Pad until length is a 2 pow
    last_val = last(dist_p_tups)[1]
    while !ispow2(length(dist_p_tups))
        push!(dist_p_tups, (last_val, 0.))
    end

    prefix_sums = accumulate(+, [p for (d, p) in dist_p_tups])
    function helper(i, j)
        if i == j
            dist_p_tups[i][1]
        else
            first_half_end = (i + j - 1) ÷ 2
            first_half_p = prefix_sums[first_half_end] - prefix_sums[i] + dist_p_tups[i][2]
            total_p = prefix_sums[j] - prefix_sums[i] + dist_p_tups[i][2]
            @dice_ite if flip(first_half_p/total_p)
                helper(i, first_half_end)
            else
                helper(first_half_end+1, j)
            end
        end
    end
    helper(1, length(dist_p_tups))
end

function discrete_sbk(dist_p_tups)
    dist_p_tups = collect(dist_p_tups)
    @assert sum(p for (d, p) in dist_p_tups) ≈ 1 "Probabilities must sum to 1"

    v = Dict()
    p_sum = 1.
    for (val, weight) in dist_p_tups
        v[val] = weight/p_sum
        p_sum -= weight
    end

    ans = last(dist_p_tups)[1]
    for i = (length(dist_p_tups) - 1):-1:1
        (val, weight) = dist_p_tups[i]
        ans = @dice_ite if flip(v[val]) val else ans end
    end
    return ans
end
