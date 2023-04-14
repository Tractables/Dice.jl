using Test
using Dice
using Dice: Flip, ifelse, num_ir_nodes
using Distributions

@testset "Gaussian observations" begin
    datapt = DistFixedPoint{6, 2}(0.0)
    code = @dice begin
                a = flip(0.5)
                gaussian_observe(DistFixedPoint{6, 2}, 4, -4.0, 4.0, 0.0, 1.0, datapt)
                a
    end

    @test pr(code)[false] ≈ 0.5

    # test for conjugate gaussians
    datapt = DistFixedPoint{8, 3}(1.0)
    map([true, false]) do add_arg
        code = @dice begin
                    a = continuous(DistFixedPoint{8, 3}, Normal(0, 1), 16, -8.0, 8.0)
                    gaussian_observe(DistFixedPoint{8, 3}, 16, -8.0, 8.0, a, 1.0, datapt, add=add_arg)
                    a
        end
        @test expectation(code) ≈ 0.5
    end

    # no warning test for different gaussian observes
    datapt = DistFixedPoint{10, 2}(1.0)
    map([true, false]) do mult_arg
        code = @dice begin
                    a = continuous(DistFixedPoint{10, 2}, Normal(4, 1), 16, 0.25, 8.25)
                    gaussian_observe(DistFixedPoint{10, 2}, 16, -8.0, 8.0, 0.0, a, datapt, mult=mult_arg)
                    a
        end
        @test_nowarn pr(code)
    end

    map([true, false]) do mult_arg
        code = @dice begin
                    m = uniform(DistFixedPoint{10, 2}, -4.0, 4.0)
                    s = continuous(DistFixedPoint{10, 2}, Normal(4, 1), 16, 0.25, 8.25)
                    gaussian_observe(DistFixedPoint{10, 2}, 16, -8.0, 8.0, m, s, datapt, mult=mult_arg)
                    m
        end
        @test_nowarn pr(code)
    end

    datapt = 0.0
    code = @dice begin
                m = uniform(DistFixedPoint{4, 2}, -1.0, 1.0)
                s = uniform(DistFixedPoint{4, 2}, -1.0, 1.0)
                gaussian_observe_enumerate(DistFixedPoint{4, 2}, [datapt], m, s)
                m
            end
    @test_nowarn pr(code)
end

@testset "Parametrised Flip" begin
    l = Vector(undef, 10)
    for i=1:10
        a = parametrised_flip(DistFixedPoint{5 + i, 3+i}(0.7))
        p = pr(a)
        l[i] = 0.7 - p[1.0]
    end
    @show l
    @test reverse(l) == sort(l)

end

@testset "CDF_overapproximate" begin
    DFiP = DistFixedPoint{6, 3}
    dist = uniform(DFiP, 0.0, 4.0)
    limit = 1.253
    @test cdf_overapproximate(dist, limit) == pr(dist < DFiP(1.375))
end