using Dice
using Test
using Dice: Flip, num_ir_nodes

@testset "DistIntOH inference" begin
    x = DistIntOH{-8, 4}([false, false, true, false]) # -6
    @test Dice.bitwidth(x) == 4

    p = pr(x)
    @test p[-5] ≈ 0
    @test p[-6] ≈ 1
    @test p[-7] ≈ 0
   
    x = uniform(DistIntOH{-4, 8})
    p = pr(x)
    @test issetequal(keys(p), -(4):(3))
    @test all(values(p) .≈ 1/8)

    x = uniform(DistIntOH{-8, 16}, 8)
    p = pr(x)
    @test x isa DistIntOH{-8, 16}
    @test issetequal(keys(p), -8:-1)
    @test all(values(p) .≈ 1/8)

    @test_throws Exception DistIntOH{3}([false, false, true, false])
    @test_throws Exception DistIntOH{5}([false, false, true, false])

    ps1, ps2 = pr(uniform(DistIntOH{-4, 8}), uniform(DistUInt{2}))
    @test issetequal(keys(ps1), -(2^2):(2^2-1))
    @test all(values(ps1) .≈ 1/2^3)

    x = DistIntOH{-3, 6}([false, false, true, false, false, false]) # -1
    y = DistIntOH{-3, 6}([false, false, false, false, false, true]) # 2
    p = pr(ifelse(flip(0.1), x, y))
    @test p[-1] ≈ 0.1
    @test p[2] ≈ 0.9

    @test prob_equals(x, DistIntOH{-3, 6}(-1))
    @test prob_equals(y, DistIntOH{-3, 6}(2))
end

# @testset "DistIntOH casting" begin
#     y = DistIntOH{4}([flip(0.5), false, true, true])
#     z = convert(y, DistIntOH{5})
#     p1 = pr(z)
#     p2 = pr(y)
#     @test p1 == p2

#     z = convert(y, DistIntOH{3})
#     p = pr(z)
#     @test p[3] ≈ 1.0
# end

# @testset "DistIntOH expectation" begin
#     y = DistIntOH{4}([true, false, true, false])
#     @test expectation(y) == -6.0
#     @test expectation(@dice y) == -6.0
#     @test variance(y) == 0.0
#     @test variance(@dice y) == 0.0

#     y = DistIntOH{2}([flip(0.1), flip(0.1)])
#     p = pr(y)
#     mean = reduce(+, [(key*value) for (key, value) in p])
#     @test expectation(y) ≈ mean
#     std_sq = reduce(+, [(key*key*value) for (key, value) in p]) - mean^2
#     @test variance(y) ≈ std_sq

#     x = uniform(DistIntOH8)
#     p = pr(x)
#     @test expectation(x) ≈ -0.5
#     std_sq = reduce(+, [(key*key*value) for (key, value) in p]) - (-0.5)^2
#     @test variance(x) ≈ std_sq
    
#     y = prob_equals(x, DistIntOH8(42))
#     @test expectation(x; evidence=y) ≈ 42
#     @test variance(x; evidence = y) ≈ 0.0

#     y = prob_equals(x, DistIntOH8(-42))
#     @test expectation(x; evidence=y) ≈ -42
#     @test variance(x; evidence = y) ≈ 0.0
# end


@testset "DistIntOH arithmetic" begin
    # a = DistIntOH{3}(3)
    # b = DistIntOH{3}(3)
    # @test_throws Exception pr(a + b)

    # a = DistIntOH{3}(-3)
    # b = DistIntOH{3}(-3)
    # @test_throws Exception pr(a + b)

    a = DistIntOH{-3,7}(-3)
    b = DistIntOH{-3,7}(3)
    p = pr(a + b)
    @test p[0] == 1

    # a = uniform(DistIntOH{3}, 3)
    # b = DistIntOH{3}(-1)
    # @test_throws Exception p = pr(@dice a + b)

    # a = DistIntOH{3}(3)
    # b = DistIntOH{3}(-2)
    # @test_throws Exception pr(a - b)

    # a = DistIntOH{3}(-3)
    # b = DistIntOH{3}(2)
    # @test_throws Exception pr(a - b)

    a = DistIntOH{1, 3}(3)
    b = DistIntOH{1, 3}(2)
    p = pr(a - b)
    @test p[1] == 1

    a = DistIntOH{-4, 4}(-3)
    b = DistIntOH{-4, 4}(-2)
    p = pr(a - b)
    @test p[-1] == 1

    a = uniform(DistIntOH{-4, 6}, -3, 1)
    b = DistIntOH{-4, 6}(1)
    p = pr(a - b)
    @test issetequal(keys(p), -4:-1)
    @test all(values(p) .≈ 1/2^2)

    # T = DistIntOH{2}
    # x = uniform(T,1) - T(1)
    # y = uniform(T,1) - T(1)
    # @test pr(@dice x + y)[-1] ≈ 0.5
    # @test pr(x + y)[-1] ≈ 0.5

    # we want overallocation of bits to not affect the computation graph size
    # B = 30
    # T = DistIntOH{B}
    # x = uniform(T,1) - T(1)
    # y = uniform(T,1) - T(1)
    # s = convert(x.number, DistUInt{B+1}) + convert(y.number, DistUInt{B+1})
    # @test Dice.num_ir_nodes(s.bits[2]) < 15 
    
end

@testset "DistIntOH multiply" begin

    a = DistIntOH{-8, 20}(2)
    b = DistIntOH{-8, 20}(-3)
    p = pr(a*b)
    @test p[-6] ≈ 1

    a = DistIntOH{-4, 12}(-2)
    b = DistIntOH{-4, 12}(-3)
    p = pr(@dice a*b)
    @test p[6] ≈ 1

    a = DistIntOH{-4, 12}(2)
    b = DistIntOH{-4, 12}(3)
    p = pr(a*b)
    @test p[6] ≈ 1

    a = DistIntOH{-8, 20}(-2)
    b = DistIntOH{-8, 20}(3)
    p = pr(a*b)
    @test p[-6] ≈ 1

    a = uniform(DistIntOH{-4, 9}, -2, 2)
    b = uniform(DistIntOH{-4, 9}, -2, 2)
    p = pr(@dice a*b)
    @test p[4] ≈ 1/16
    @test p[0] ≈ 7/16

    for i = -8:7
        for j = -8:7
            a = DistIntOH{-8, 16}(i)
            b = DistIntOH{-8, 16}(j)
            c = @dice a*b
            if (i*j > 7) | (i*j < -8)
                # @test_throws ProbException pr(c)
            else
                @test pr(c)[i*j] ≈ 1.0
            end
        end
    end
end

@testset "DistIntOH uniform" begin
    y = @dice uniform(DistIntOH{-8, 16}, -7, 1)
    p = pr(y)
  
    @test issetequal(keys(p), -7:1:1-1)
    @test all(values(p) .≈ 1/8)

    y = @dice uniform(DistIntOH{-8, 16}, -7, 3)
    p = pr(y)
  
    @test issetequal(keys(p), -7:1:3-1)
    @test all(values(p) .≈ 1/10)

    # @test_throws Exception y = uniform(DistIntOH{-8, 16}, -7, 9)
end

@testset "DistIntOH division" begin
    x = DistIntOH{-8, 16}(7)
    y = DistIntOH{-8, 16}(-3)
    p = pr(@dice x / y)
    @test p[-2] ≈ 1.0

    # a = uniform(DistIntOH{-4, 8}, -4, 4)
    # b = uniform(DistIntOH{-4, 8}, -4, 4)
    # @test_throws ProbException pr(@dice a/b)

    x = DistIntOH{-5, 8}(-4)
    y = DistIntOH{-5, 8}(-4)
    p = pr(@dice x / y)
    @test p[1] ≈ 1.0

    for i = -4:3
        for j = -4:3
            a = DistIntOH{-4, 8}(i)
            b = DistIntOH{-4, 8}(j)
            if (j == 0) | ((i == -4) & (j == -1))
                # @test_throws ProbException pr(@dice a/b)
            else
                @test pr(@dice a/b)[i ÷ j] ≈ 1.0
            end
        end
    end
end

@testset "DistIntOH mod" begin
    x = DistIntOH{-8, 16}(7)
    y = DistIntOH{-8, 16}(-3)
    p = pr(@dice x % y)
    @test p[1] ≈ 1.0

    # a = uniform(DistIntOH{3}, -4, 4)
    # b = uniform(DistIntOH{3}, -4, 4)
    # @test_throws ProbException pr(@dice a%b)

    x = DistIntOH{-4, 8}(-4)
    y = DistIntOH{-4, 8}(-4)
    p = pr(@dice x % y)
    @test p[0] ≈ 1.0

    for i = -4:3
        for j = -4:3
            a = DistIntOH{-4, 8}(i)
            b = DistIntOH{-4, 8}(j)
            if (j == 0)
                # @test_throws ProbException pr(@dice a%b)
            else
                @test pr(@dice a%b)[i % j] ≈ 1.0
            end
        end
    end
end

@testset "DistIntOH isless" begin
    x = DistIntOH{-8, 16}(3)
    y = DistIntOH{-8, 16}(-7)
    p = pr(x < y)
    @test p[0.0] ≈ 1.0

    x = uniform(DistIntOH{-2, 6}, 0, 2)
    y = uniform(DistIntOH{-2, 6}, 0, 2)
    p = pr(x < y)
    @test p[1.0] ≈ 0.25

    x = uniform(DistIntOH{-3, 6}, -2, 2)
    y = DistIntOH{-3, 6}(0)
    p = pr(x < y)
    @test p[1] ≈ 1/2

    for i = -4:3
        for j = -4:3
            a = DistIntOH{-4, 8}(i)
            b = DistIntOH{-4, 8}(j)
            @test pr(@dice a < b)[i < j] ≈ 1.0
        end
    end

end
