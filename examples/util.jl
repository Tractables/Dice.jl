function print_dict(d; top_n=20)
    top_n === nothing && (top_n = length(d))
    truncated = top_n < length(d)

    d = sort(collect(d), by= xv -> -xv[2])  # by decreasing probability
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
