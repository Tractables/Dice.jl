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

    # test for conjugate gaussians
    map([true, false]) do add_arg
        code = @dice begin
                    a = continuous(DistFixedPoint{8, 3}, Normal(0, 1), 16, -8.0, 8.0)
                    gaussian_observe(DistFixedPoint{8, 3}, 16, -8.0, 8.0, a, 1.0, 1.0, add=add_arg)
                    a
        end
        @test expectation(code) ≈ 0.5
    end

    # no warning test for different gaussian observes
    map([true, false]) do mult_arg
        code = @dice begin
                    a = continuous(DistFixedPoint{10, 2}, Normal(4, 1), 16, 0.25, 8.25)
                    gaussian_observe(DistFixedPoint{10, 2}, 16, -8.0, 8.0, 0.0, a, 1.0, mult=mult_arg)
                    a
        end
        @test_nowarn pr(code)
    end

    map([true, false]) do mult_arg
        code = @dice begin
                    m = uniform(DistFixedPoint{10, 2}, -4.0, 4.0)
                    s = continuous(DistFixedPoint{10, 2}, Normal(4, 1), 16, 0.25, 8.25)
                    gaussian_observe(DistFixedPoint{10, 2}, 16, -8.0, 8.0, m, s, 1.0, mult=mult_arg)
                    m
        end
        @test_nowarn pr(code)
    end
end