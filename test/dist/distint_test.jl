using Test
using Dice

@testset "DistInt" begin
    
    x = DistInt{4}([true, false, true, false])
    @test Dice.bitwidth(x) == 4

    p = pr(x)
    @test p[4] ≈ 0
    @test p[5] ≈ 1
    @test p[6] ≈ 0
   
    x = uniform(DistInt{3})
    p = pr(x)
    @test issetequal(keys(p), 0:(2^3-1))
    @test all(values(p) .≈ 1/2^3)
    
end
