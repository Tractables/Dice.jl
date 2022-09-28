using Test
using Dice
using Dice: Flip, ifelse, num_ir_nodes

@testset "Gaussian observations" begin
    code = @dice begin
                a = flip(0.5)
                gaussian_observe(DistFixedPoint{6, 2}, 4, -4.0, 4.0, 0.0, 1.0, 0.0)
                a
    end

    @test pr(code)[false] ≈ 0.5
    
    
end