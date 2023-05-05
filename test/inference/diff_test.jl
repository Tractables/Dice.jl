using Test
using Dice

@testset "MLE" begin
    reset_flips!()
    x = flip_for("?") & flip_for("?") & !flip_for("?")
    train_group_probs!([x])
    @test get_group_prob("?") ≈ 2/3

    b = @dice_ite if flip_for("?") true else flip(0.5) end
    dataset = [true, true, false]
    bools_to_maximize = [prob_equals(b, x) for x in dataset]
    train_group_probs!(bools_to_maximize)
    @test get_group_prob("?") ≈ 1/3

    x = flip_for("a") & flip_for("b") & !flip_for("c")
    train_group_probs!([x])
    @test get_group_prob("a") > .99
    @test get_group_prob("b") > .99
    @test get_group_prob("c") < .01
end

@testset "MLE iterations deterministic" begin
    dataset = [true, true, false]
    
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
