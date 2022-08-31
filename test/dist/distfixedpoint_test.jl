using Test
using Dice
using Dice: Flip, ifelse, num_ir_nodes
using Distributions

@testset "DistFixedPoint inference" begin
    x = DistFixedPoint{4, 2}([true, false, true, false]) # -1.5
    @test Dice.bitwidth(x) == 4

    p = pr(x)
    @test p[-1.25] ≈ 0
    @test p[-1.5] ≈ 1
    @test p[-1.75] ≈ 0

    x = DistFixedPoint{4, 2}(1.53)
    @test Dice.bitwidth(x) == 4

    p = pr(x)
    @test p[1.5] ≈ 1
    @test p[-1.5] ≈ 0
   
    x = uniform(DistFixedPoint{3, 1})
    p = pr(x)
    @test issetequal(keys(p), -(2^2)/2:1/2:(2^2-1)/2)
    @test all(values(p) .≈ 1/2^3)

    @test_throws Exception DistFixedPoint{4, 5}([true, false, true, false])
    @test_throws Exception DistFixedPoint{3, 2}([true, false, true, false])

    x = DistFixedPoint{4, 1}([true, false, true, false]) # -3
    y = DistFixedPoint{4, 1}([false, false, true, true]) # 1.5
    p = pr(ifelse(flip(0.1), x, y))
    @test p[-3] ≈ 0.1
    @test p[1.5] ≈ 0.9

    @test prob_equals(x, DistFixedPoint{4, 1}(-3.0))
    @test prob_equals(y, DistFixedPoint{4, 1}(1.5))
end

@testset "DistFixedPoint expectation" begin
    y = DistFixedPoint{4, 3}([true, false, true, false])
    @test expectation(y) == -0.75

    y = DistFixedPoint{2, 0}([flip(0.1), flip(0.1)])
    p = pr(y)
    mean = reduce(+, [(key*value) for (key, value) in p])
    @test expectation(y) ≈ mean

end

@testset "DistFixedPoint triangle and continuous" begin
    @test_throws Exception y = triangle(DistFixedPoint{4, 3}, 4)
    y = triangle(DistFixedPoint{4, 3}, 3)
    p = pr(y)
    n = 2^3
    for i=0:7
        @test p[i/n] ≈ 2*i/(n*(n-1))
    end

    y = continuous(DistFixedPoint{4, 2}, Normal(0, 1), 2, -2.0, 2.0)
end

@testset "DistFixedPoint arithmetic" begin
    a = DistFixedPoint{3, 1}(1.5)
    b = DistFixedPoint{3, 1}(1.5)
    @test_throws Exception pr(a + b)

    a = DistFixedPoint{3, 1}(-1.5)
    b = DistFixedPoint{3, 1}(-1.5)
    @test_throws Exception pr(a + b)

    a = DistFixedPoint{3, 1}(-1.5)
    b = DistFixedPoint{3, 1}(1.5)
    p = pr(a + b)
    @test p[0] == 1

    a = uniform(DistFixedPoint{3, 1}, 3)
    b = DistFixedPoint{3, 1}(-0.5)
    @test_throws ProbException p = pr(@dice a + b)
end
