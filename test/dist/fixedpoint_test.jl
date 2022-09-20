using Test
using Dice
using Dice: Flip, ifelse, num_ir_nodes
using Distributions

@testset "DistFixedPoint inference" begin
    x = DistFixedPoint{4, 2}([true, false, true, false]) # -1.5
    @test Dice.bitwidth(x) == 4

    p = pr(x)
    @test p[-1.25] ≈ 0
    @test p[-1.5] ≈ 1
    @test p[-1.75] ≈ 0

    x = DistFixedPoint{4, 2}(1.53)
    @test Dice.bitwidth(x) == 4

    p = pr(x)
    @test p[1.5] ≈ 1
    @test p[-1.5] ≈ 0
   
    x = uniform(DistFixedPoint{3, 1})
    p = pr(x)
    @test issetequal(keys(p), -(2^2)/2:1/2:(2^2-1)/2)
    @test all(values(p) .≈ 1/2^3)

    @test_throws Exception DistFixedPoint{4, 5}([true, false, true, false])
    @test_throws Exception DistFixedPoint{3, 2}([true, false, true, false])

    x = DistFixedPoint{4, 1}([true, false, true, false]) # -3
    y = DistFixedPoint{4, 1}([false, false, true, true]) # 1.5
    p = pr(ifelse(flip(0.1), x, y))
    @test p[-3] ≈ 0.1
    @test p[1.5] ≈ 0.9

    @test prob_equals(x, DistFixedPoint{4, 1}(-3.0))
    @test prob_equals(y, DistFixedPoint{4, 1}(1.5))

    y = DistFixedPoint{11, 2}(-0.045840)
    @test pr(y)[-0.25] ≈ (1.0)
end

@testset "DistFixedPoint expectation" begin
    y = DistFixedPoint{4, 3}([true, false, true, false])
    @test expectation(y) == -0.75

    y = DistFixedPoint{2, 0}([flip(0.1), flip(0.1)])
    p = pr(y)
    mean = reduce(+, [(key*value) for (key, value) in p])
    @test expectation(y) ≈ mean

end

@testset "DistFixedPoint triangle" begin
    y = triangle(DistFixedPoint{4, 3}, 3)
    p = pr(y)
    n = 2^3
    for i=0:7
        @test p[i/n] ≈ 2*i/(n*(n-1))
    end
end

@testset "DistFixedPoint arithmetic" begin
    a = DistFixedPoint{3, 1}(1.5)
    b = DistFixedPoint{3, 1}(1.5)
    @test_throws Exception pr(a + b)

    a = DistFixedPoint{3, 1}(-1.5)
    b = DistFixedPoint{3, 1}(-1.5)
    @test_throws Exception pr(a + b)

    a = DistFixedPoint{3, 1}(-1.5)
    b = DistFixedPoint{3, 1}(1.5)
    p = pr(a + b)
    @test p[0] == 1

    a = uniform(DistFixedPoint{3, 1}, 3)
    b = DistFixedPoint{3, 1}(-0.5)
    @test_throws ProbException p = pr(@dice a + b)

    a = DistFixedPoint{3, 1}(1.5)
    b = DistFixedPoint{3, 1}(-1.0)
    @test_throws Exception pr(a - b)

    a = DistFixedPoint{3, 1}(-1.5)
    b = DistFixedPoint{3, 1}(1.0)
    @test_throws Exception pr(a - b)

    a = DistFixedPoint{3, 1}(1.5)
    b = DistFixedPoint{3, 1}(1.0)
    p = pr(a - b)
    @test p[0.5] == 1

    a = DistFixedPoint{3, 1}(-1.5)
    b = DistFixedPoint{3, 1}(-1.0)
    p = pr(a - b)
    @test p[-0.5] == 1

    a = uniform(DistFixedPoint{3, 1}, 2)
    b = DistFixedPoint{3, 1}(0.5)
    p = pr(a - b)
    @test issetequal(keys(p), -0.5:0.5:1.0)
    @test all(values(p) .≈ 1/2^2)
end

@testset "DistFixedPoint continuous" begin
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
    d = Truncated(Normal(1, 1), -1.0, 3.0)
    lower = -1.0
    q = Vector{Float64}(undef, 2^4)
    for i=1:2^4
        q[i] = cdf(d, lower + 0.25) - cdf(d, lower)
        lower += 0.25
    end 

    kl_vector = [0.0, 0.0, 0.0, 0.0]
    map(pieces) do piece
        y = continuous(DistFixedPoint{5, 2}, Normal(1, 1), piece, -1.0, 3.0)
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
    y = continuous(DistFixedPoint{5, 2}, Normal(1, 1), 8, -1.0, 3.0)
    p = pr(y)
    p2 = map(a -> a[2], sort([(k, v) for (k, v) in p]))
    @test p2 ≈ q

    #TODO: write tests for continuous distribution other than gaussian
end

@testset "DistFixedPoint multiply" begin
    a = [0.5, 0.5, -0.5, -0.5]
    b = [0.75, -0.75, 0.75, -0.75]
    map(a, b) do i, j
        fi = DistFixedPoint{4, 2}(i)
        fj = DistFixedPoint{4, 2}(j)
        p = pr(@dice fi*fj; ignore_errors=true)
        @test p[i*j] ≈ 1
    end

    a = uniform(DistFixedPoint{4, 2}, 2) - DistFixedPoint{4, 2}(0.5)
    b = uniform(DistFixedPoint{4, 2}, 2) - DistFixedPoint{4, 2}(0.5)
    p = pr(@dice a*b; ignore_errors=true)
    @test p[0.25] ≈ 1/16
    @test p[0] ≈ 7/16
end

@testset "DistFixedPoint casting" begin
    y = DistFixedPoint{4, 2}([true, false, true, false])
    p1 = pr(y)

    z = convert(y, DistFixedPoint{5, 2})
    p2 = pr(z)
    @test p1 == p2

    z = convert(y, DistFixedPoint{5, 3})
    p2 = pr(z)
    @test p1 == p2

    z = convert(y, DistFixedPoint{3, 1})
    p2 = pr(z)
    @test p1 == p2

    z = convert(y, DistFixedPoint{3, 2})
    p2 = pr(z)
    @test p2[0.5] ≈ 1.0
end
