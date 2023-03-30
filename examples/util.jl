function print_dict(d; top_n=20)
    top_n === nothing && (top_n = length(d))
    truncated = top_n < length(d)

    d = sort(collect(d), by= xv -> (-xv[2], xv[1]))  # by decreasing probability, increasing key
    truncated && (d = d[1:top_n])  # truncate
    d = [(to_str_pretty(k), v) for (k, v) in d]  # print trees/tups/vectors more nicely

    widest = if length(d) > 0 maximum(length(string(k)) for (k, _) in d) else 0 end
    for (i, (k, v)) in enumerate(d)
        println("   $(rpad(k, widest, ' ')) => $(v)")
    end
    if truncated
        println("   $(rpad('⋮', widest, ' ')) => ⋮")
    end
end

to_str_pretty(x) = string(x)
to_str_pretty(x::Vector) = "[" * join((to_str_pretty(y) for y in x), ", ") * "]"
to_str_pretty(x::Tuple) = "(" * join((to_str_pretty(y) for y in x), ", ") * ")"

function get_char_freqs_from_url(corpus_url)
    corpus = join(c for c in lowercase(read(download(corpus_url), String)) if c in valid_chars)
    counts = Dict([(c, 0) for c in valid_chars])
    for c in corpus
        counts[c] += 1
    end
    [counts[c]/length(corpus) for c in valid_chars]
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
