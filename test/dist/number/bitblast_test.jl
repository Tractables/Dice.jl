using Test
using Dice
using Dice: Flip, ifelse, num_ir_nodes
using Distributions

@testset "DistFix triangle" begin
    y = triangle(DistFix{4, 3}, 3)
    p = pr(y)
    n = 2^3
    for i=0:7
        @test p[i/n] ≈ 2*i/(n*(n-1))
    end
end

@testset "DistFix bitblast" begin
    pieces = [1, 2, 4, 8]
    function kl_divergence(p, q)
        @test sum(p) ≈ 1.0
        @test sum(q) ≈ 1.0
        ans = 0
        l = length(p)
        for i=1:l
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
    kl_vector2 = [0.0, 0.0, 0.0, 0.0]
    map(pieces) do piece
        y = bitblast(DistFix{5, 2}, Normal(1, 1), piece, -1.0, 3.0)
        p = pr(y)

        z = bitblast_exponential(DistFix{5, 2}, Normal(1, 1), piece, -1.0, 3.0)
        p_z = pr(z)

        # Symmetric gaussian around mean
        for i=1:0.25:2.75
            @test p[i] ≈ p[-i+1.75]
        end

        # probability below mean
        @test sum(values(filter(p -> first(p) < 1, p))) ≈ 0.5

        # decreasing kl divergence with pieces
        p = map(a -> a[2], sort([(k, v) for (k, v) in p]))
        kl_vector[Int(log2(piece))+1] = kl_divergence(p, q)

        p_z = map(a -> a[2], sort([(k, v) for (k, v) in p_z]))
        kl_vector2[Int(log2(piece))+1] = kl_divergence(p_z, q)
    end

    @show kl_vector
    @show kl_vector2

    @test issorted(kl_vector, rev=true)
    @test issorted(kl_vector2, rev = true)
    
    # Exactness for maximum number of pieces
    y = bitblast(DistFix{5, 2}, Normal(1, 1), 8, -1.0, 3.0)
    p = pr(y)
    p2 = map(a -> a[2], sort([(k, v) for (k, v) in p]))
    @test p2 ≈ q

    # Negative F
    y = bitblast(DistFix{5, -1}, Normal(1, 1), 2, -4.0, 4.0)
    p = pr(y)
    d = truncated(Normal(1, 1), -4, 4)
    for i in keys(p)
        @test p[i] ≈ cdf(d, i+2) - cdf(d, i)
    end

    #TODO: write tests for continuous distribution other than gaussian
    #TODO: Write tests for exponential pieces
end

@testset "DistFix bitblast sample" begin
    d = truncated(Normal(0, 1), -8.0, 8.0)
    offset = 0.0625
    width = 0.0625
    dist = bitblast_sample(DistFix{5, 1}, d, 32, -8.0, 8.0, offset=offset, width=width)
    p = pr(dist)
    total_prob = 0.0
    for i in keys(p)
        total_prob += cdf(d, i + offset + width) - cdf(d, i + offset)
    end
    for i in keys(p)
        @test p[i] ≈ (cdf(d, i + offset + width) - cdf(d, i + offset))/total_prob
    end
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

@testset "DistFix exponential" begin
    x = unit_exponential(DistFix{5, 3}, 1.0)
    @test pr(x)[0.125] ≈ exp(0.125)*(exp(1/8) - 1)/(exp(1) - 1)
    
    x = unit_exponential(DistFix{10, 9}, -1.0)
    @test pr(x)[0.125] ≈ exp(-0.125)*(exp(-1/2^9) - 1)/(exp(-1) - 1) 
    
    x = unit_exponential(DistFix{10, 9}, -1.0; reverse=true)
    @test pr(x)[0.125] ≈ exp(-0.125)*(exp(-1/2^9) - 1)/(exp(-1) - 1)

    x = exponential(DistFix{6, 3}, 1.0, 0.0, 2.0)
    y = unit_exponential(DistFix{6, 4}, 2.0)
    @test sum([pr(x)[i] ≈ pr(y)[i/2] for i in 0:0.125:1.875]) == 16 

    x = exponential(DistFix{6, 3}, 1.0, -1.0, 1.0; reverse=true)
    @test sum([pr(x)[i] ≈ pr(y)[(i+1)/2] for i in -1:0.125:0.875]) == 16
end

@testset "DistFix laplace, unit_gamma" begin
    x = laplace(DistFix{10, 3}, 0.0, 1.0, -8.0, 8.0)
    y = exponential(DistFix{10, 3}, -1.0, 0.0, 8.0)
    @test pr(x)[1]*2 ≈ pr(y)[1]

    actual_dist = Truncated(Laplace(0.0, 1.0), -8.0, 8.0)
    @test pr(x)[0] ≈ cdf(actual_dist, 0.125) - cdf(actual_dist, 0.0)

    # Tests for Gamma distribution (α = 1)
    x = @dice unit_gamma(DistFix{5, 3}, 0, -1.0)
    a = pr(x)

    d = Truncated(Gamma(1, 1), 0.0, 1.0)
    @test a[0] ≈ (cdf(d, 0.125) - cdf(d, 0))

    x = @dice unit_gamma(DistFix{5, 3}, 0, -3.0)
    a = pr(x)

    d = Truncated(Gamma(1, 1/3), 0.0, 1.0)
    @test a[0] ≈ (cdf(d, 0.125) - cdf(d, 0))

    # Tests for Gamma distribution for (α = 2)
    x = @dice unit_gamma(DistFix{5, 3}, 1, -1.0)
    a = pr(x)
    d = Truncated(Gamma(2, 1), 0.0, 1.0)
    @test a[0] ≈ cdf(d, 0.125) - cdf(d, 0)

    x = @dice unit_gamma(DistFix{5, 3}, 1, -3.0)
    a = pr(x)
    d = Truncated(Gamma(2, 1/3), 0.0, 1.0)
    @test a[0] ≈ cdf(d, 0.125) - cdf(d, 0)

    #Tests for shift_point_gamma
    x = @dice shift_point_gamma(DistFix{5, 3}, 1, 1.0)
    a = pr(x)
    @test a[0.125]/a[0] ≈ 2exp(0.125)

    x = @dice shift_point_gamma(DistFix{5, 3}, 2, -2.0)
    a = pr(x)
    @test a[0.125]/a[0] ≈ 4exp(-0.25)

    # Building Gamma(3, 0.5)
    x = (@dice unit_gamma(DistFix{4, 3}, 2, -2.0, constants = []))
    a = pr(x)[0.0]
    d = Truncated(Gamma(3, 0.5), 0.0, 1.0)
    @test a ≈ cdf(d, 0.125) - cdf(d, 0.0)
    #TODO test for beta = 0
    #TODO test for positive beta

    # Truncated Geometric
    x = Truncated(Geometric(0.8), 0, 32)
    @test_throws Exception a = geometric(DistFix{6, 2}, 0.8, 32)
    a = geometric(DistFix{8, 2}, 0.8, 32)
    @test pr(a)[0.0] ≈ pdf(x, 0.0)
    @test pr(a)[19] ≈ pdf(x, 19.0)

    x = (@dice general_gamma(DistFix{7, 4}, 1, 1.0, 0.5, 1.0))
    @test pr(x)[0.0] ≈ 0.0
end

@testset "DistFix n_unit_exponentials" begin
    v = n_unit_exponentials(DistFix{5, 3}, [1.0, -1.0])
    v1 = unit_exponential(DistFix{5, 3}, 1.0)
    v2 = unit_exponential(DistFix{5, 3}, -1.0)

    @test sum([pr(v[1])[i] ≈ pr(v1)[i] for i in 0.0:0.125:0.875]) == 8
    @test sum([pr(v[2])[i] ≈ pr(v2)[i] for i in 0.0:0.125:0.875]) == 8
end

