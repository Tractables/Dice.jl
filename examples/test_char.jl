using Dice

c = @dice begin
    if flip(1/10)
        DistChar('a')
    elseif flip(2/9)
        DistChar('D')
    elseif flip(3/7)
        DistChar(' ')
    else
        DistChar('!')
    end
end

dist = infer(c)
@assert sum(values(dist)) ≈ 1
@assert dist['a'] ≈ 1/10
@assert dist['D'] ≈ 2/10
@assert dist[' '] ≈ 3/10
@assert dist['!'] ≈ 4/10

c = @dice begin
    if flip(1/10)
        DistChar('a')
    elseif flip(2/9)
        DistChar('b')
    elseif flip(3/7)
        DistChar('c')
    else
        DistChar('b')
    end
end
@assert infer_bool(c < DistChar('b')) ≈ 1/10
@assert infer_bool(c <= DistChar('b')) ≈ 7/10
@assert infer_bool(c >= DistChar('b')) ≈ 9/10
@assert infer_bool(c > DistChar('b')) ≈ 3/10