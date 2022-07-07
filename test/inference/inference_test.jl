using Test
using Dice

@testset "Backend selection" begin
    @test pr(flip(0.78), Dice.Cudd()) ≈ 0.78
    @test pr(true, Dice.Cudd()) ≈ 1.00
end