using Dice
using Revise

# Test four ways to construct
cg = @dice begin
    DistTree(DistInt(5), DistVector{DistTree{DistInt}}([
        DistTree(DistInt(3))
    ]))
end
dist = infer(cg)
@assert dist[(5, [(3, [])])] == 1
@assert length(dist) == 1

cg = @dice begin
    DistTree(DistInt(5))
end
dist = infer(cg)
@assert dist[(5, [])] == 1
@assert length(dist) == 1


cg = @dice begin
    DistTree{DistInt}(DistInt(5), DistVector{DistTree{DistInt}}([
        DistTree(DistInt(3))
    ]))
end
dist = infer(cg)
@assert dist[(5, [(3, [])])] == 1
@assert length(dist) == 1

cg = @dice begin
    DistTree{DistInt}(DistInt(5))
end
dist = infer(cg)
@assert dist[(5, [])] == 1
@assert length(dist) == 1


# Test prob_append_child, ifelse
cg = @dice begin
    t = DistTree(DistInt(5))
    if flip(0.4)
        prob_append_child(t, DistTree(DistInt(3)))
    else
        t
    end
end
dist = infer(cg)
@assert dist[(5, [(3, [])])] ≈ 0.4
@assert dist[(5, [])] ≈ 0.6
@assert length(dist) == 2


# Test prob_extend_children
cg = @dice begin
    t = DistTree(DistInt(5))
    if flip(0.4)
        prob_extend_children(
            t,
            DistVector([DistTree(DistInt(3)), DistTree(DistInt(4))])
        )
    else
        t
    end
end
dist = infer(cg)
@assert dist[(5, [(3, []), (4, [])])] ≈ 0.4
@assert dist[(5, [])] ≈ 0.6
@assert length(dist) == 2

# Test prob_equals
cg = @dice begin
    t = DistTree(DistInt(5))
    t = if flip(0.4)
        prob_extend_children(
            t,
            DistVector([DistTree(DistInt(3)), DistTree(DistInt(4))])
        )
    else
        t
    end
    prob_equals(
        t,
        DistTree(DistInt(5), DistVector([DistTree(DistInt(3)), DistTree(DistInt(4))]))
    )
end
@assert infer_bool(cg) ≈ 0.4

# Test leaves
cg = @dice begin
    t = DistTree(DistInt(5))
    leaves(if flip(0.4)
        prob_extend_children(
            t,
            DistVector([DistTree(DistInt(3)), DistTree(DistInt(4))])
        )
    else
        t
    end)
end
dist = infer(cg)
@assert dist[[3, 4]] ≈ 0.4
@assert dist[[5]] ≈ 0.6
@assert length(dist) == 2
