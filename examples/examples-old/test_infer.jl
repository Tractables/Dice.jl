using Alea
code = @dice_ite begin
    b = DistInt(7)
    f = flip(0.2)
    [!f, (if f DistInt(3) else DistInt(7) end, f)]
end
dist, err = infer(code)
@assert err == 0
@assert sum(v for v in values(dist)) ≈ 1
@assert dist[[true, (7, false)]] ≈ 0.8
@assert dist[[false, (3, true)]] ≈ 0.2

code = @dice_ite begin
    # four-sided die
    die = safe_add(DistInt(1), DistInt([flip(0.5), flip(0.5)]))
    odd = die.bits[1]
    at_most_three = die < 4
    die, odd, at_most_three
end
die, odd, at_most_three = code
@assert @Pr(die)[1] ≈ 1/4
@assert @Pr(die | at_most_three)[1] ≈ 1/3
@assert @Pr(at_most_three) ≈ 3/4
@assert @Pr(odd | at_most_three) ≈ 2/3

t, f = @dice_ite begin
    flip(true), flip(false)
end
@assert @Pr(t) == 1
@assert @Pr(f) == 0

i, f = @dice_ite begin
    f = flip(0.3)
    i = DWE(DistInt(2)) + if f DistInt(1) else DistInt(2) end
    i, f
end
dist, err = @Pr(i | f)  # infer_with_observation(i, f)
@assert dist[3] == 1
@assert length(dist) == 1
@assert err == 0

i, f = @dice_ite begin
    f = flip(0.3)
    i = DWE(DistInt(2)) + if f DistInt(1) else DistInt(2) end
    i = if flip(0.1) i / DistInt(0) else i end
    i, f
end
dist, err = @Pr(i | f)  # infer_with_observation(i, f)
@assert dist[3] ≈ 0.9
@assert length(dist) == 1
@assert err ≈ 0.1
