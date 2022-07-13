using Test
using Dice

@testset "DistInt inference" begin
    
    x = DistInt{4}([true, false, true, false]) # 10
    @test Dice.bitwidth(x) == 4

    p = pr(x)
    @test p[9] ≈ 0
    @test p[10] ≈ 1
    @test p[11] ≈ 0
   
    x = uniform(DistInt{3})
    p = pr(x)
    @test issetequal(keys(p), 0:(2^3-1))
    @test all(values(p) .≈ 1/2^3)

    x = uniform(DistInt{4}, 3)
    p = pr(x)
    @test x isa DistInt{4}
    @test issetequal(keys(p), 0:(2^3-1))
    @test all(values(p) .≈ 1/2^3)

    x = DistInt([true, false, true, false])
    @test Dice.bitwidth(x) == 4

    @test_throws Exception DistInt{3}([true, false, true, false])
    @test_throws Exception DistInt{5}([true, false, true, false])

    ps1, ps2 = pr(uniform(DistInt{3}), uniform(DistInt{2}))
    @test issetequal(keys(ps1), 0:(2^3-1))
    @test all(values(ps1) .≈ 1/2^3)
    @test issetequal(keys(ps2), 0:(2^2-1))
    @test all(values(ps2) .≈ 1/2^2)

end

@testset "DistInt arithmetic" begin
    
    x = DistInt{4}([true, false, true, false]) # 10
    y = DistInt{4}([false, false, true, true]) # 3
    p = pr(x + y)
    @test p[12] ≈ 0
    @test p[13] ≈ 1
    @test p[14] ≈ 0

    z = uniform(DistInt{4}, 3)
    p = pr(z + y)
    @test issetequal(keys(p), 3 .+ (0:(2^3-1)))
    @test all(values(p) .≈ 1/2^3)


    w = uniform(DistInt{4}, 3)
    p = pr(z + w)
    n = 2^3
    for i=0:(2^4-1)
        @test p[i] ≈ (n - abs(i-(n-1)))/n^2
    end
end
