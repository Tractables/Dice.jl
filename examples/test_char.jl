using Dice

code = @dice begin
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
bdd = compile(code)
dist = infer(bdd)
@assert sum(values(dist)) ≈ 1
@assert dist['a'] ≈ 1/10
@assert dist['D'] ≈ 2/10
@assert dist[' '] ≈ 3/10
@assert dist['!'] ≈ 4/10

code = @dice begin
    c1 = if flip(1/10)
        DistChar('a')
    elseif flip(2/9)
        DistChar('b')
    else
        DistChar('c')
    end
    c1 < DistChar('b')
end
bdd = compile(code)
@assert infer(bdd) ≈ 1/10
