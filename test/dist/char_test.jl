using Test
using Alea

@testset "DistChar core" begin
    c = @alea_ite begin
        if flip(1/10)
            DistChar('a')
        elseif flip(2/9)
            DistChar('D')
        elseif flip(3/7)
            DistChar(' ')
        else
            DistChar('!')
        end
    end

    dist = pr(c)

    @test sum(values(dist)) ≈ 1
    @test dist['a'] ≈ 1/10
    @test dist['D'] ≈ 2/10
    @test dist[' '] ≈ 3/10
    @test dist['!'] ≈ 4/10

    c = @alea_ite begin
        if flip(1/10)
            DistChar('a')
        elseif flip(2/9)
            DistChar('b')
        elseif flip(3/7)
            DistChar('c')
        else
            DistChar('b')
        end
    end
    @test pr(c < DistChar('b'))[true] ≈ 1/10
    @test pr(c <= DistChar('b'))[true] ≈ 7/10
    @test pr(c >= DistChar('b'))[true] ≈ 9/10
    @test pr(c > DistChar('b'))[true] ≈ 3/10
end
