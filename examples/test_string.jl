using Dice

# Test concatenation, appending, ifelse
cg = @dice begin
    s = if flip(3/5) DistString("sand") else DistString("san") end
    s = if flip(2/3) s + 'd' else s end
    t = if flip(1/10) DistString("wich") else DistString("box") end
    s + t
end
dist = infer(cg)
@assert sum(values(dist)) ≈ 1
@assert dist["sandwich"] ≈ 7/150
@assert dist["sandbox"] ≈ 21/50
@assert dist["sanwich"] ≈ 1/75
@assert dist["sanbox"] ≈ 3/25
@assert dist["sanddwich"] ≈ 1/25
@assert dist["sanddbox"] ≈ 9/25
@assert infer_bool(prob_equals(cg, "sandwich")) ≈ 7/150


# Test concatenation for empty strings
cg = @dice begin
    DistString("") + DistString("")
end
dist = infer(cg)
@assert sum(values(dist)) ≈ 1
@assert dist[""] ≈ 1


# Test getindex, setindex
cg = @dice begin
    s = DWE(if flip(0.6) DistString("abc") else DistString("xyz") end)

    # Choose whether to change index 1 (Pr=0.3) or 2 (Pr = 0.7)
    i = DWE(if flip(0.3) DistInt(1) else DistInt(2) end)

    c = DWE(if flip(0.1) DistChar('d') else DistChar('e') end)
    s = prob_setindex(s, i, c)
    prob_equals(DWE(DistString("aec")), s)
end
dist, err = infer(cg)
@assert dist[true] ≈ 0.6*0.7*0.9
@assert err ≈ 0

# Test lessthan
cg = @dice begin
    s = if flip(0.6) DistString("abc") else DistString("xyz") end
    t = if flip(0.6) DistString("abc") else DistString("xyz") end
    s < t
end
@assert infer_bool(cg) ≈ 0.6 * 0.4


# Test lessthan for identical strings
cg = @dice begin
    DistString("abc") < DistString("abc")
end
@assert infer_bool(cg) ≈ 0


# Test lessthan for strings that differ only in length
cg = @dice begin
    DistString("abc") < DistString("abca")
end
@assert infer_bool(cg) ≈ 1
