using Dice

code = @dice begin
    b = DistInt(7)
    f = flip(0.2)
    [!f, (if f DistInt(3) else DistInt(7) end, f)]
end

bdd = compile(code)
dist = infer(bdd)
@assert sum(v for v in values(dist)) ≈ 1
@assert dist[[true, (7, false)]] ≈ 0.8
@assert dist[[false, (3, true)]] ≈ 0.2
