using Test
using Dice
using Dice: Flip, num_ir_nodes

@testset "DistInt inference" begin
    x = DistInt{4}([true, false, true, false]) # -6
    @test Dice.bitwidth(x) == 4

    p = pr(x)
    @test p[-5] ≈ 0
    @test p[-6] ≈ 1
    @test p[-7] ≈ 0
   
    x = uniform(DistInt{3})
    p = pr(x)
    @test issetequal(keys(p), -(2^2):(2^2-1))
    @test all(values(p) .≈ 1/2^3)

    x = uniform(DistInt{4}, 3)
    p = pr(x)
    @test x isa DistInt{4}
    @test issetequal(keys(p), 0:(2^3-1))
    @test all(values(p) .≈ 1/2^3)

    @test_throws Exception DistInt{3}([true, false, true, false])
    @test_throws Exception DistInt{5}([true, false, true, false])

    ps1, ps2 = pr(uniform(DistInt{3}), uniform(DistUInt{2}))
    @test issetequal(keys(ps1), -(2^2):(2^2-1))
    @test all(values(ps1) .≈ 1/2^3)

    x = DistInt{4}([true, false, true, false]) # -6
    y = DistInt{4}([false, false, true, true]) # 3
    p = pr(ifelse(flip(0.1), x, y))
    @test p[-6] ≈ 0.1
    @test p[3] ≈ 0.9

    @test prob_equals(x, DistInt{4}(-6))
    @test prob_equals(y, DistInt{4}(3))
end

@testset "DistInt casting" begin
    y = DistInt{4}([flip(0.5), false, true, true])
    z = convert(y, DistInt{5})
    p1 = pr(z)
    p2 = pr(y)
    @test p1 == p2

    z = convert(y, DistInt{3})
    p = pr(z)
    @test p[3] ≈ 1.0
end

@testset "DistInt expectation" begin
    y = DistInt{4}([true, false, true, false])
    @test expectation(y) == -6.0

    y = DistInt{2}([flip(0.1), flip(0.1)])
    p = pr(y)
    mean = reduce(+, [(key*value) for (key, value) in p])
    @test expectation(y) ≈ mean

end

@testset "DistInt triangle" begin
    y = triangle(DistInt{4}, 3)
    p = pr(y)
    n = 2^3
    for i=0:7
        @test p[i] ≈ 2*i/(n*(n-1))
    end
end

@testset "DistInt arithmetic" begin
    a = DistInt{3}(3)
    b = DistInt{3}(3)
    @test_throws Exception pr(a + b)

    a = DistInt{3}(-3)
    b = DistInt{3}(-3)
    @test_throws Exception pr(a + b)

    a = DistInt{3}(-3)
    b = DistInt{3}(3)
    p = pr(a + b)
    @test p[0] == 1

    a = uniform(DistInt{3}, 3)
    b = DistInt{3}(-1)
    @test_throws Exception p = pr(@dice a + b)

    a = DistInt{3}(3)
    b = DistInt{3}(-2)
    @test_throws Exception pr(a - b)

    a = DistInt{3}(-3)
    b = DistInt{3}(2)
    @test_throws Exception pr(a - b)

    a = DistInt{3}(3)
    b = DistInt{3}(2)
    p = pr(a - b)
    @test p[1] == 1

    a = DistInt{3}(-3)
    b = DistInt{3}(-2)
    p = pr(a - b)
    @test p[-1] == 1

    a = uniform(DistInt{3}, 2)
    b = DistInt{3}(1)
    p = pr(a - b)
    @test issetequal(keys(p), -1:2)
    @test all(values(p) .≈ 1/2^2)
end
