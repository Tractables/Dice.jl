using Test
using Dice, Distributions

@testset "Gaussian observations" begin
    
    FP = DistFixedPoint{6, 2}
    data = FP(0.0)
    
    code = @dice begin
        a = flip(0.5)
        gaussian_observe(FP, 4, -4.0, 4.0, 0.0, 1.0, data)
        a
    end

    @test pr(code)[false] ≈ 0.5

    FP = DistFixedPoint{8, 2}
    data = FP(1.0)

    # test for conjugate gaussians
    map([true, false]) do add_arg
        code = @dice begin
            a = continuous(FP, Normal(0, 1), 16, -8.0, 8.0)
            gaussian_observe(FP, 8, -8.0, 8.0, a, 1.0, data, add=add_arg)
            a
        end
        @test isapprox(expectation(code), 0.5;) rtol=0.02
    end

    FP = DistFixedPoint{5, 1}
    data = FP(1.0)

    map([true, false]) do mult_arg

        code = @dice begin
            a = continuous(FP, Normal(1, 1), 2, 0.5, 2.5)
            gaussian_observe(FP, 2, -2.0, 2.0, 0.0, a, data, mult=mult_arg)
            a
        end
        @test 1.2 < expectation(code) < 1.6

        code = @dice begin
            m = uniform(FP, -2.0, 2.0)
            a = continuous(FP, Normal(1, 1), 2, 0.5, 2.5)
            gaussian_observe(FP, 2, -2.0, 2.0, m, a, data, mult=mult_arg)
            m
        end
        @test expectation(code) > 0.1

    end

end

@testset "Parametrised Flip" begin
    l = Vector(undef, 10)
    for i=1:10
        a = parametrised_flip(DistFixedPoint{5 + i, 3+i}(0.7))
        p = pr(a)
        l[i] = 0.7 - p[1.0]
    end
    @test reverse(l) == sort(l)

end