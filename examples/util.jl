function print_dict(d)
    println("$(typeof(d)) with $(length(d)) entries")
    widest = if length(d) > 0 maximum(length(string(k)) for (k, _) in d) else 0 end
    for (k, v) in d
        println("   $(rpad(k, widest, ' ')) => $(v)")
    end
end