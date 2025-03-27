using Test
using Alea

@testset "DistEnum core" begin
    @enum Colors red green blue
    cg = @dice_ite begin
        if flip(1/10)
            DistEnum(red)
        else
            if flip(2/9)
                DistEnum(green)
            else
                DistEnum(blue)
            end
        end
    end
    dist = pr(cg)
    @test sum(values(dist)) ≈ 1
    @test dist[red] ≈ 1/10
    @test dist[green] ≈ 2/10
    @test dist[blue] ≈ 7/10

    cg = @dice_ite begin
        x = if flip(1/10)
            DistEnum(red)
        elseif flip(2/9)
            DistEnum(green)
        else
            DistEnum(blue)
        end
        y = if flip(1/10)
            DistEnum(red)
        elseif flip(2/9)
            DistEnum(green)
        else
            DistEnum(blue)
        end
        prob_equals(x, y)
    end
    @test pr(cg)[true] ≈ (1/10)^2 + (2/10)^2 + (7/10)^2
end
