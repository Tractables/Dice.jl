using Test
using Dice

@testset "Backend selection" begin
    @test pr(flip(0.78); algo = Dice.Cudd())[true] ≈ 0.78
    @test pr(true; algo = Dice.Cudd())[true] ≈ 1.00
end

@testset "Multiple queries" begin

    x = flip(0.2) | flip(0.8)
    y = flip(0.1) | flip(0.3)
    evidence = x | y | flip(0.5)

    denom = 1-prod(1 .- [0.2,0.8,0.1,0.3,0.5])
    @test pr(evidence)[true] ≈ denom
    
    p1, p2 = pr(x, y; evidence)
    @test p1[true] ≈ (1-(1-0.2)*(1-0.8)) / denom
    @test p2[true] ≈ (1-(1-0.1)*(1-0.3)) / denom

end

@testset "Joint queries" begin

    x = flip(0.2)
    y = flip(0.1)
    prs = pr(JointQuery([x,y]))
    
    @test sum(x -> x[2], prs) ≈ 1
    @test length(prs) == 4

    prs = pr(JointQuery([x,y,!x]))
    @test sum(x -> x[2], prs) ≈ 1
    @test length(prs) == 4

    prs = pr(JointQuery([x,!x]))
    @test sum(x -> x[2], prs) ≈ 1
    @test length(prs) == 2

    prs = pr(JointQuery([x,y,flip(0.5)]))
    @test sum(x -> x[2], prs) ≈ 1
    @test length(prs) == 8

    prs1, prs2 = pr(JointQuery([x,y]), JointQuery([x,flip(0.5)]))
    @test sum(x -> x[2], prs1) ≈ 1
    @test sum(x -> x[2], prs2) ≈ 1
    @test length(prs1) == 4
    @test length(prs2) == 4

    prs = pr(JointQuery([x,y]); evidence = (x | y))
    @test sum(x -> x[2], prs) ≈ 1
    @test length(prs) == 3

    prs = pr(JointQuery([x,y]); evidence = (x & y))
    @test sum(x -> x[2], prs) ≈ 1
    @test length(prs) == 1

end