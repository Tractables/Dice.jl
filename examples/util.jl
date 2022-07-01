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

# Prints trees as returned from inference on DistTree
# tree := (val, [tree, tree, tree...])
function print_tree(t; indent_per_level=4)
    @assert indent_per_level >= 1
    print_tree_helper(t, [], 0, false, indent_per_level)
end

function print_tree_helper(t, pipes, level, last_child, indent_per_level)
    # Print padding
    padding_size = level * indent_per_level
    if level > 0
        padding = [' ' for _ in 1:padding_size]
        for pipe in pipes
            padding[pipe] = '│'
        end
        # Connect last pipe to value
        padding[last(pipes)] = if last_child '└' else '├' end
        for i in (last(pipes)+1):(padding_size-1)
            padding[i] = '─'
        end
        print(join(padding))
    end

    # Print value
    println(t[1])
    
    # Consume last pipe if we are last child, always create new pipe below us
    inherited_pipes = copy(pipes)
    if last_child
        pop!(inherited_pipes)
    end
    push!(inherited_pipes, padding_size + 1)

    for i in 1:length(t[2])
        print_tree_helper(
            t[2][i],
            inherited_pipes,
            level + 1,
            i == length(t[2]),
            indent_per_level
        )
    end
end

function get_char_freqs_from_url(corpus_url)
    corpus = join(c for c in lowercase(read(download(corpus_url), String)) if c in valid_chars)
    counts = Dict([(c, 0) for c in valid_chars])
    for c in corpus
        counts[c] += 1
    end
    [counts[c]/length(corpus) for c in valid_chars]
end
