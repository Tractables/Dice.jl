using Dice

c = @dice_ite begin
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

dist = pr(c)

@assert sum(values(dist)) ≈ 1
@assert dist['a'] ≈ 1/10
@assert dist['D'] ≈ 2/10
@assert dist[' '] ≈ 3/10
@assert dist['!'] ≈ 4/10

c = @dice_ite begin
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
@assert pr(c < DistChar('b'))[true] ≈ 1/10
@assert pr(c <= DistChar('b'))[true] ≈ 7/10
@assert pr(c >= DistChar('b'))[true] ≈ 9/10
@assert pr(c > DistChar('b'))[true] ≈ 3/10
