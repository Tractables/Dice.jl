using Test

using Dice

@testset "Sugar Tests" begin

    @test infer((@dice prob_equals(uniform(dicecontext(), 2, DistInt), 0)), :bdd) ≈ 0.25
    @test infer((@dice prob_equals(triangle(dicecontext(), 2, DistInt), 0)), :bdd) ≈ 0.0
    @test infer((@dice prob_equals(discrete2(dicecontext(), [0.1, 0.2, 0.3, 0.4], DistInt), 0)), :bdd) ≈ 0.1
    @test infer((@dice prob_equals(anyline(dicecontext(), 2, 0.1, DistInt), 3)), :bdd) ≈ 0.4

end