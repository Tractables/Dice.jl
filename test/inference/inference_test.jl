using Test
using Dice

@testset "Backend selection" begin
    @test pr(flip(0.78); algo = Dice.Cudd()) ≈ 0.78
    @test pr(true; algo = Dice.Cudd()) ≈ 1.00
end

@testset "Multiple queries" begin

    x = flip(0.2) | flip(0.8)
    y = flip(0.1) | flip(0.3)
    z = x | y | flip(0.5)

    denom = 1-prod(1 .- [0.2,0.8,0.1,0.3,0.5])
    @test pr(z) ≈ denom
    @test condprobs([x,y]; evidence = z) ≈ [(1-(1-0.2)*(1-0.8)), (1-(1-0.1)*(1-0.3))] ./ denom

end