using Test
using Dice
using Dice: Flip, ifelse, num_ir_nodes
using Distributions

@testset "DistFix inference" begin
    x = DistFix{4, 2}([true, false, true, false]) # -1.5
    @test Dice.bitwidth(x) == 4

    p = pr(x)
    @test p[-1.25] ≈ 0
    @test p[-1.5] ≈ 1
    @test p[-1.75] ≈ 0

    x = DistFix{4, 2}(1.53)
    @test Dice.bitwidth(x) == 4

    p = pr(x)
    @test p[1.5] ≈ 1
    @test p[-1.5] ≈ 0
   
    x = uniform(DistFix{3, 1})
    p = pr(x)
    @test issetequal(keys(p), -(2^2)/2:1/2:(2^2-1)/2)
    @test all(values(p) .≈ 1/2^3)

    @test_throws Exception DistFix{4, 5}([true, false, true, false])
    @test_throws Exception DistFix{3, 2}([true, false, true, false])

    x = DistFix{4, 1}([true, false, true, false]) # -3
    y = DistFix{4, 1}([false, false, true, true]) # 1.5
    p = pr(ifelse(flip(0.1), x, y))
    @test p[-3] ≈ 0.1
    @test p[1.5] ≈ 0.9

    @test prob_equals(x, DistFix{4, 1}(-3.0))
    @test prob_equals(y, DistFix{4, 1}(1.5))

    y = DistFix{11, 2}(-0.045840)
    @test pr(y)[-0.25] ≈ (1.0)
end

@testset "DistFix expectation" begin
    y = DistFix{4, 3}([true, false, true, false])
    @test expectation(y) == -0.75
    @test expectation(@dice y) == -0.75
    @test variance(y) == 0.0
    @test variance(@dice y) == 0.0

    y = DistFix{2, 0}([flip(0.1), flip(0.1)])
    p = pr(y)
    mean = reduce(+, [(key*value) for (key, value) in p])
    std_sq = reduce(+, [(key*key*value) for (key, value) in p]) - mean^2
    @test expectation(y) ≈ mean
    @test expectation(@dice y) ≈ mean
    @test variance(y) ≈ std_sq
    @test variance(@dice y) ≈ std_sq
end

@testset "DistFix triangle" begin
    y = triangle(DistFix{4, 3}, 3)
    p = pr(y)
    n = 2^3
    for i=0:7
        @test p[i/n] ≈ 2*i/(n*(n-1))
    end
end

@testset "DistFix arithmetic" begin
    a = DistFix{3, 1}(1.5)
    b = DistFix{3, 1}(1.5)
    @test_nowarn pr(a + b)
    @test_throws Exception pr(@dice a + b)

    a = DistFix{3, 1}(-1.5)
    b = DistFix{3, 1}(-1.5)
    @test_nowarn pr(a + b)
    @test_throws Exception pr(@dice a + b)

    a = DistFix{3, 1}(-1.5)
    b = DistFix{3, 1}(1.5)
    p = pr(a + b)
    @test p[0] == 1

    a = uniform(DistFix{3, 1}, 3)
    b = DistFix{3, 1}(-0.5)
    @test_throws ProbException p = pr(@dice a + b)

    a = DistFix{3, 1}(1.5)
    b = DistFix{3, 1}(-1.0)
    @test_nowarn pr(a - b)
    @test_throws Exception pr(@dice a - b)

    a = DistFix{3, 1}(-1.5)
    b = DistFix{3, 1}(1.0)
    @test_nowarn pr(a - b)
    @test_throws Exception pr(@dice a - b)

    a = DistFix{3, 1}(1.5)
    b = DistFix{3, 1}(1.0)
    p = pr(a - b)
    @test p[0.5] == 1

    a = DistFix{3, 1}(-1.5)
    b = DistFix{3, 1}(-1.0)
    p = pr(a - b)
    @test p[-0.5] == 1

    a = uniform(DistFix{3, 1}, 2)
    b = DistFix{3, 1}(0.5)
    p = pr(a - b)
    @test issetequal(keys(p), -0.5:0.5:1.0)
    @test all(values(p) .≈ 1/2^2)
end

@testset "DistFix continuous" begin
    pieces = [1, 2, 4, 8]
    function kl_divergence(p, q)
        @assert sum(p) ≈ 1.0
        @assert sum(q) ≈ 1.0
        ans = 0
        for i=1:length(p)
            if p[i] > 0
                ans += p[i] *(log(p[i]) - log(q[i]))
            end
        end
        ans
    end
    d = truncated(Normal(1, 1), -1.0, 3.0)
    lower = -1.0
    q = Vector{Float64}(undef, 2^4)
    for i=1:2^4
        q[i] = cdf(d, lower + 0.25) - cdf(d, lower)
        lower += 0.25
    end 

    kl_vector = [0.0, 0.0, 0.0, 0.0]
    map(pieces) do piece
        y = bitblast(DistFix{5, 2}, Normal(1, 1), piece, -1.0, 3.0)
        p = pr(y)

        # Symmetric gaussian around mean
        for i=1:0.25:2.75
            @test p[i] ≈ p[-i+1.75]
        end

        # probability below mean
        @test sum(values(filter(p -> first(p) < 1, p))) ≈ 0.5

        # decreasing kl divergence with pieces
        p = map(a -> a[2], sort([(k, v) for (k, v) in p]))
        kl_vector[Int(log2(piece))+1] = kl_divergence(p, q)

    end
    @test issorted(kl_vector, rev=true)
    
    # Exactness for maximum number of pieces
    y = bitblast(DistFix{5, 2}, Normal(1, 1), 8, -1.0, 3.0)
    p = pr(y)
    p2 = map(a -> a[2], sort([(k, v) for (k, v) in p]))
    @test p2 ≈ q

    #TODO: write tests for continuous distribution other than gaussian
end

@testset "DistFix multiply" begin
    #TODO: make sure if the tests convey the intended meaning of multiply
    a = [0.5, 0.5, -0.5, -0.5]
    b = [0.75, -0.75, 0.75, -0.75]
    map(a, b) do i, j
        fi = DistFix{4, 2}(i)
        fj = DistFix{4, 2}(j)
        p = pr(@dice fi*fj)
        @test p[floor(i*j * 2^2)/4] ≈ 1
    end

    a = uniform(DistFix{4, 2}, 2) - DistFix{4, 2}(0.5)
    b = uniform(DistFix{4, 2}, 2) - DistFix{4, 2}(0.5)
    p = pr(@dice a*b)
    @test p[0.25] ≈ 1/16
    @test p[0] ≈ 11/16

    a = DistFix{20, 0}(14.0) * DistFix{20, 0}(-7.0)
    p = pr(@dice a)
    @test p[-98.0] ≈ 1.0

    for i = -2.0:0.25:2-0.25
        for j = -2.0:0.25:2-0.25
            a = DistFix{4, 2}(i)
            b = DistFix{4, 2}(j)
            c = @dice a*b
            d = floor(i*j *4)/4
            if (d > 1.75) | (d < -2)
                @test_throws ProbException pr(c)
            else
                if floor(i*j *4)/4 == 0.0
                    @test pr(c)[0.0] ≈ 1.0
                else
                    @test pr(c)[floor(i*j *4)/4] ≈ 1.0
                end
            end
        end
    end
end

@testset "DistFix casting" begin
    y = DistFix{4, 2}([true, false, true, false])
    p1 = pr(y)

    z = convert(DistFix{5, 2}, y)
    p2 = pr(z)
    @test p1 == p2

    z = convert(DistFix{5, 3}, y)
    p2 = pr(z)
    @test p1 == p2

    z = convert(DistFix{3, 1}, y)
    p2 = pr(z)
    @test p1 == p2

    z = convert(DistFix{3, 2}, y)
    p2 = pr(z)
    @test p2[0.5] ≈ 1.0
end

@testset "DistFix uniform" begin
    y = uniform(DistFix{7, 3}, -3.0, 1.0)
    p = pr(y)
  
    @test issetequal(keys(p), -3.0: 1/8 : (1.0-1/8))
    @test all(values(p) .≈ 1/2^5)

    y = uniform(DistFix{7, 3}, -3.0, 0.125)
    p = pr(y)
  
    @test issetequal(keys(p), -3.0 : 1/8 : (0.125-1/8))
    @test all(values(p) .≈ 1/25)

    y = uniform(DistFix{6, 2}, -1.1, 2.3)
    p = pr(y)
    @test issetequal(keys(p), -1.25 : 0.25 : 2.25)

    y = uniform(DistFix{6, 2}, -1.100000001, 2.2499999999)
    p = pr(y)
    @test issetequal(keys(p), -1.25 : 0.25 : 2.00)

    y = uniform(DistFix{6, 2}, -1.0999999999, 2.2500000001)
    p = pr(y)
    @test issetequal(keys(p), -1.25 : 0.25 : 2.00)

    flags = [:ite, :arith]
    map(flags) do flag
        y = uniform(DistFix{7, 3}, -3.0, 1.0; strategy=flag)
        p = pr(y)
    
        @test issetequal(keys(p), -3.0:1/8:1.0 - 1/8)
        @test all(values(p) .≈ 1/2^5)
    end
end

@testset "DistFix division" begin
    x = DistFix{5, 2}(0.5)
    y = DistFix{5, 2}(2.0)
    c = @dice x/y
    q = pr(c)

    for i = -4.0:0.25:4 - 0.25
        for j= -4.0:0.25:4 - 0.25
            x = DistFix{5, 2}(i)
            y = DistFix{5, 2}(j)
            c = @dice x/y
            ans = sign(i/j) * floor(abs(i/j) * 4)/4
            if (j == 0.0) | (ans >= 4.0) | (ans < -4.0)
                @test_throws ProbException pr(c)
            else
                if ans == -0.0
                    @test pr(c)[0.0] ≈ 1.0
                else
                    @test pr(c)[ans] ≈ 1.0
                end
            end
        end
    end
end

@testset "DistFix isless" begin
    x = DistFix{4, 2}(0.75)
    y = DistFix{4, 2}(-1.75)
    p = pr(x < y)
    @test p[0.0] ≈ 1.0

    x = uniform(DistFix{3, 1}, 0.0, 1.0)
    y = uniform(DistFix{3, 1}, 0.0, 1.0)
    p = pr(x < y)
    @test p[1.0] ≈ 0.25

    for i = -2:0.5:1.5
        for j = -2:0.5:1.5
            a = DistFix{3, 1}(i)
            b = DistFix{3, 1}(j)
            @test pr(@dice a < b)[i < j] ≈ 1.0
        end
    end

end
 
