using Test
using Dice

@testset "Backend selection" begin
    @test pr(flip(0.78); algo = Dice.Cudd()) ≈ 0.78
    @test pr(true; algo = Dice.Cudd()) ≈ 1.00
end