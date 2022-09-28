using Test
using Dice
using Dice: Flip, ifelse, num_ir_nodes
using Distributions

@testset "Gaussian observations" begin
    code = @dice begin
                a = flip(0.5)
                gaussian_observe(DistFixedPoint{6, 2}, 4, -4.0, 4.0, 0.0, 1.0, 0.0)
                a
    end

    @test pr(code)[false] ≈ 0.5

    map([true, false]) do add_arg
        code = @dice begin
                    a = continuous(DistFixedPoint{8, 3}, Normal(0, 1), 16, -8.0, 8.0)
                    gaussian_observe(DistFixedPoint{8, 3}, 16, -8.0, 8.0, a, 1.0, 1.0, add=add_arg)
                    a
        end
        @test expectation(code) ≈ 0.5
    end
    
    
end