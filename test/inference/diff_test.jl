using Test
using Dice

@testset "MLE" begin
    reset_flips!()
    b = @dice_ite if flip_for("?") true else flip_for("?") end
    train_group_probs!([prob_equals(b, x) for x in dataset], 200)
    p1 = pr(b)[true]

    reset_flips!()
    b = @dice_ite if flip_for("?") true else flip_for("?") end
    train_group_probs!([prob_equals(b, x) for x in dataset], 100)
    train_group_probs!([prob_equals(b, x) for x in dataset], 100)
    p2 = pr(b)[true]

    @test p1 ≈ p2
end
