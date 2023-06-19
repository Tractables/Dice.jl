using Test
using Dice
using CUDD

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

@testset "Cudd debug info assignment" begin
    f = flip(0.5)
    debug_info_ref = Ref{CuddDebugInfo}()
    pr(f, algo=Cudd())
    pr(f, algo=Cudd(reordering_type=CUDD.CUDD_REORDER_SIFT))
    @test !isassigned(debug_info_ref)

    # only assign when we pass in a ref
    pr(f, algo=Cudd(debug_info_ref=debug_info_ref))
    @test isassigned(debug_info_ref)
end

@testset "Cudd auto reordering" begin
    fs = [flip(0.5) for _ in 1:60]
    xs = Vector{Any}(undef, 60)
    xs[1] = flip(0.5)
    for i in 2:60
        temp = fs[i] | fs[i ÷ 2]
        xs[i] = temp & xs[i - 1]
    end
    x = last(xs)

    debug_info_ref = Ref{CuddDebugInfo}()

    # The numbers of nodes could change, we are really just checking that
    # changing the reordering type is doing something.

    pr(x, algo=Cudd(debug_info_ref=debug_info_ref))
    @test debug_info_ref[].num_nodes == 196604

    pr(x, algo=Cudd(CUDD.CUDD_REORDER_NONE, debug_info_ref))
    @test debug_info_ref[].num_nodes == 196604

    pr(x, algo=Cudd(CUDD.CUDD_REORDER_SIFT, debug_info_ref))
    @test debug_info_ref[].num_nodes == 160

    pr(x, algo=Cudd(CUDD.CUDD_REORDER_WINDOW2, debug_info_ref))
    @test debug_info_ref[].num_nodes == 129820
end
