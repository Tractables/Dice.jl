using Alea

N = 5

md = @dice begin
    row_col_pairs = [
        (uniform(DistInt32, 1, 1 + N), uniform(DistInt32, 1, 1 + N))
        for _ in 1:N
    ]

    for (i1, (row1, col1)) in enumerate(row_col_pairs)
        for (i2, (row2, col2)) in enumerate(row_col_pairs)
            i1 == i2 && continue
            # Check row conflicts
            observe(!prob_equals(row1, row2))
            # Check column conflicts
            observe(!prob_equals(col1, col2))
            # Check conflicts along one diagonal
            observe(!prob_equals(row1 + col1, row2 + col2))
            # Check conflicts along other diagonal
            observe(!prob_equals(row1 - col1, row2 - col2))
        end
    end    
    row_col_pairs
end

dist = pr(md)  # 1200 entries, we distinguished between different orderings...
projection = Set(Set(world) for world in keys(dist))  # 10 true placements
