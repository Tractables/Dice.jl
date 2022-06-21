using Dice

# Test concatenation, appending, ifelse
cg = @dice_ite begin
    v = if flip(3/5)
        DistVector([DistInt(1),DistInt(2),DistInt(3),DistInt(4)])
    else
        DistVector([DistInt(7),DistInt(6),DistInt(5)])
    end
    v = if flip(2/3) prob_append(v, DistInt(100)) else v end
    v2 = if flip(1/10)
        DistVector([DistInt(333), DistInt(444)])
    else
        DistVector([DistInt(555)])
    end
    prob_extend(v, v2)
end
dist = infer(cg)
@assert sum(values(dist)) ≈ 1
@assert dist[[1, 2, 3, 4, 100, 333, 444]] ≈ 3/5 * 2/3 * 1/10
@assert dist[[1, 2, 3, 4, 100, 555]] ≈ 3/5 * 2/3 * 9/10
@assert dist[[1, 2, 3, 4, 333, 444]] ≈ 3/5 * 1/3 * 1/10
@assert dist[[1, 2, 3, 4, 555]] ≈ 3/5 * 1/3 * 9/10
@assert dist[[7, 6, 5, 100, 333, 444]] ≈ 2/5 * 2/3 * 1/10
@assert dist[[7, 6, 5, 100, 555]] ≈ 2/5 * 2/3 * 9/10
@assert dist[[7, 6, 5, 333, 444]] ≈ 2/5 * 1/3 * 1/10
@assert dist[[7, 6, 5, 555]] ≈ 2/5 * 1/3 * 9/10


# Test concatenation for empty vectors
cg = @dice_ite begin
    prob_extend(DistVector{DistInt}(), DistVector{DistInt}())
end
dist = infer(cg)
@assert sum(values(dist)) ≈ 1
@assert dist[[]] ≈ 1


cg = @dice_ite begin
    prob_extend(DistVector{DistString}(Vector{DistString}()), [DistString("hi")])
end
dist = infer(cg)
@assert sum(values(dist)) ≈ 1
@assert dist[["hi"]] ≈ 1


# Test getindex, setindex
cg = @dice_ite begin
    s = if flip(0.6)
        DistVector(Vector{DistBool}([flip(false), flip(false), flip(false)]))
    else
        DistVector(Vector{DistBool}([flip(true), flip(true)]))
    end

    # Choose whether to change index 1 (Pr=0.3) or 2 (Pr = 0.7)
    f1 = flip(0.3)
    i = DistInt([f1, !f1])

    c = if flip(0.1) flip(false) else flip(true) end
    s = prob_setindex(DWE(s), DWE(i), DWE(c))
    prob_equals(DWE(DistVector([flip(false), flip(true), flip(false)])), s)
end
dist, error = infer(cg)
@assert dist[true] ≈ 0.6*0.7*0.9
@assert error ≈ 0

# Test prob_startswith
cg = @dice_ite begin
    s = DistVector(DistBool[flip(false), flip(0.3), flip(false)])
    t = DistVector(DistBool[flip(false), flip(true)])
    prob_startswith(s, t)
end
@assert infer_bool(cg) ≈ 0.3

cg = @dice_ite begin
    s = DistVector(DistBool[flip(false)])
    s = if flip(0.3) s else prob_append(s, flip(0.4)) end
    t = DistVector(DistBool[flip(0.9), flip(true)])
    prob_startswith(s, t)
end
@assert infer_bool(cg) ≈ 0.1 * 0.7 * 0.4
