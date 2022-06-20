using Dice

dist = infer(discrete([
    (DistString("abc"), 0.3),
    (DistString(""), 0.1),
    (DistString("dice"), 0.6),
    (DistString("no"), 0.)
]))
@assert length(dist) == 3
@assert dist["abc"] ≈ 0.3
@assert dist[""] ≈ 0.1
@assert dist["dice"] ≈ 0.6

@assert infer_int(uniform_int(1:5)) ≈ [0., .2, .2, .2, .2, .2, 0., 0.]

@assert infer_int(discrete_int([.1, .2, .3, .4])) ≈ [.1, .2, .3, .4]
