using Test
using Dice
using Dice: Flip, ifelse, num_ir_nodes

@testset "DistSignedInt inference" begin
    x = DistSignedInt{4}([true, false, true, false]) # -6
    @test Dice.bitwidth(x) == 4

    p = pr(x)
    @test p[-5] ≈ 0
    @test p[-6] ≈ 1
    @test p[-7] ≈ 0
   
    x = uniform(DistSignedInt{3})
    p = pr(x)
    @test issetequal(keys(p), -(2^2):(2^2-1))
    @test all(values(p) .≈ 1/2^3)

    x = uniform(DistSignedInt{4}, 3)
    p = pr(x)
    @test x isa DistSignedInt{4}
    @test issetequal(keys(p), 0:(2^3-1))
    @test all(values(p) .≈ 1/2^3)

    @test_throws Exception DistSignedInt{3}([true, false, true, false])
    @test_throws Exception DistSignedInt{5}([true, false, true, false])

    ps1, ps2 = pr(uniform(DistSignedInt{3}), uniform(DistInt{2}))
    @test issetequal(keys(ps1), -(2^2):(2^2-1))
    @test all(values(ps1) .≈ 1/2^3)

    x = DistSignedInt{4}([true, false, true, false]) # -6
    y = DistSignedInt{4}([false, false, true, true]) # 3
    p = pr(ifelse(flip(0.1), x, y))
    @test p[-6] ≈ 0.1
    @test p[3] ≈ 0.9

    @test prob_equals(x, DistSignedInt{4}(-6))
    @test prob_equals(y, DistSignedInt{4}(3))
end

@testset "DistSignedInt casting" begin
    y = DistSignedInt{4}([flip(0.5), false, true, true])
    z = convert(y, DistSignedInt{5})
    p1 = pr(z)
    p2 = pr(y)
    @test p1 == p2

    z = convert(y, DistSignedInt{3})
    p = pr(z)
    @test p[3] ≈ 1.0
end

@testset "DistSignedInt expectation" begin
    y = DistSignedInt{4}([true, false, true, false])
    @test expectation(y) == -6.0

    y = DistSignedInt{2}([flip(0.1), flip(0.1)])
    p = pr(y)
    mean = reduce(+, [(key*value) for (key, value) in p])
    @test expectation(y) ≈ mean

end

@testset "DistSignedInt triangle" begin
    y = triangle(DistSignedInt{4}, 3)
    p = pr(y)
    n = 2^3
    for i=0:7
        @test p[i] ≈ 2*i/(n*(n-1))
    end
end

@testset "DistSignedInt arithmetic" begin
    a = DistSignedInt{3}(3)
    b = DistSignedInt{3}(3)
    @test_throws Exception pr(a + b)

    a = DistSignedInt{3}(-3)
    b = DistSignedInt{3}(-3)
    @test_throws Exception pr(a + b)

    a = DistSignedInt{3}(-3)
    b = DistSignedInt{3}(3)
    p = pr(a + b)
    @test p[0] == 1

    a = uniform(DistSignedInt{3}, 3)
    b = DistSignedInt{3}(-1)
    @test_throws Exception p = pr(@dice a + b)

    a = DistSignedInt{3}(3)
    b = DistSignedInt{3}(-2)
    @test_throws Exception pr(a - b)

    a = DistSignedInt{3}(-3)
    b = DistSignedInt{3}(2)
    @test_throws Exception pr(a - b)

    a = DistSignedInt{3}(3)
    b = DistSignedInt{3}(2)
    p = pr(a - b)
    @test p[1] == 1

    a = DistSignedInt{3}(-3)
    b = DistSignedInt{3}(-2)
    p = pr(a - b)
    @test p[-1] == 1

    a = uniform(DistSignedInt{3}, 2)
    b = DistSignedInt{3}(1)
    p = pr(a - b)
    @test issetequal(keys(p), -1:2)
    @test all(values(p) .≈ 1/2^2)
end
