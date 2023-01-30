using Dice

N = 5

md = @dice begin
    row_to_col = [
        uniform(DistInt32, 1, 1 + N)
        for _ in 1:N
    ]

    for (i1, col1) in enumerate(row_to_col)
        for (i2, col2) in enumerate(row_to_col)
            i1 == i2 && continue
            # Convert rows to Dist
            row1, row2 = DistInt32(i1), DistInt32(i2)
            # Check column conflicts
            observe(!prob_equals(col1, col2))
            # Check conflicts along one diagonal
            observe(!prob_equals(row1 + col1, row2 + col2))
            # Check conflicts along other diagonal
            observe(!prob_equals(row1 - col1, row2 - col2))
        end
    end    
    row_to_col
end

pr(md)
