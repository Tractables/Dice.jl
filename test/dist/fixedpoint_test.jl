using Test
using Dice
using Dice: Flip, ifelse, num_ir_nodes
using Distributions
using Plots
using Revise
using SymPy

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
    @test expectation(@dice y) == -0.75
    @test variance(y) == 0.0
    @test variance(@dice y) == 0.0

    y = DistFixedPoint{2, 0}([flip(0.1), flip(0.1)])
    p = pr(y)
    mean = reduce(+, [(key*value) for (key, value) in p])
    std_sq = reduce(+, [(key*key*value) for (key, value) in p]) - mean^2
    @test expectation(y) ≈ mean
    @test expectation(@dice y) ≈ mean
    @test variance(y) ≈ std_sq
    @test variance(@dice y) ≈ std_sq
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
    @test_nowarn pr(a + b)
    @test_throws Exception pr(@dice a + b)

    a = DistFixedPoint{3, 1}(-1.5)
    b = DistFixedPoint{3, 1}(-1.5)
    @test_nowarn pr(a + b)
    @test_throws Exception pr(@dice a + b)

    a = DistFixedPoint{3, 1}(-1.5)
    b = DistFixedPoint{3, 1}(1.5)
    p = pr(a + b)
    @test p[0] == 1

    a = uniform(DistFixedPoint{3, 1}, 3)
    b = DistFixedPoint{3, 1}(-0.5)
    @test_throws ProbException p = pr(@dice a + b)

    a = DistFixedPoint{3, 1}(1.5)
    b = DistFixedPoint{3, 1}(-1.0)
    @test_nowarn pr(a - b)
    @test_throws Exception pr(@dice a - b)

    a = DistFixedPoint{3, 1}(-1.5)
    b = DistFixedPoint{3, 1}(1.0)
    @test_nowarn pr(a - b)
    @test_throws Exception pr(@dice a - b)

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
        y = continuous(DistFixedPoint{5, 2}, Normal(1, 1), piece, -1.0, 3.0)
        p = pr(y)

        z = continuous(DistFixedPoint{5, 2}, Normal(1, 1), piece, -1.0, 3.0, exp=true)
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
    y = continuous(DistFixedPoint{5, 2}, Normal(1, 1), 8, -1.0, 3.0)
    p = pr(y)
    p2 = map(a -> a[2], sort([(k, v) for (k, v) in p]))
    @test p2 ≈ q

    #TODO: write tests for continuous distribution other than gaussian
    #TODO: Write tests for exponential pieces
end

@testset "DistFixedPoint multiply" begin
    #TODO: make sure if the tests convey the intended meaning of multiply
    a = [0.5, 0.5, -0.5, -0.5]
    b = [0.75, -0.75, 0.75, -0.75]
    map(a, b) do i, j
        fi = DistFixedPoint{4, 2}(i)
        fj = DistFixedPoint{4, 2}(j)
        p = pr(@dice fi*fj)
        @test p[floor(i*j * 2^2)/4] ≈ 1
    end

    a = uniform(DistFixedPoint{4, 2}, 2) - DistFixedPoint{4, 2}(0.5)
    b = uniform(DistFixedPoint{4, 2}, 2) - DistFixedPoint{4, 2}(0.5)
    p = pr(@dice a*b)
    @test p[0.25] ≈ 1/16
    @test p[0] ≈ 11/16

    a = DistFixedPoint{20, 0}(14.0) * DistFixedPoint{20, 0}(-7.0)
    p = pr(@dice a)
    @test p[-98.0] ≈ 1.0

    for i = -2.0:0.25:2-0.25
        for j = -2.0:0.25:2-0.25
            a = DistFixedPoint{4, 2}(i)
            b = DistFixedPoint{4, 2}(j)
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

@testset "DistFixedPoint casting" begin
    y = DistFixedPoint{4, 2}([true, false, true, false])
    p1 = pr(y)

    z = convert(DistFixedPoint{5, 2}, y)
    p2 = pr(z)
    @test p1 == p2

    z = convert(DistFixedPoint{5, 3}, y)
    p2 = pr(z)
    @test p1 == p2

    z = convert(DistFixedPoint{3, 1}, y)
    p2 = pr(z)
    @test p1 == p2

    z = convert(DistFixedPoint{3, 2}, y)
    p2 = pr(z)
    @test p2[0.5] ≈ 1.0
end

@testset "DistFixedPoint uniform" begin
    y = uniform(DistFixedPoint{7, 3}, -3.0, 1.0)
    p = pr(y)
  
    @test issetequal(keys(p), -3.0:1/8:1.0 - 1/8)
    @test all(values(p) .≈ 1/2^5)

    y = uniform(DistFixedPoint{7, 3}, -3.0, 0.125)
    p = pr(y)
  
    @test issetequal(keys(p), -3.0:1/8:0.125 - 1/8)
    @test all(values(p) .≈ 1/25)
   
    flags = [:ite, :arith]
    map(flags) do flag
        y = uniform(DistFixedPoint{7, 3}, -3.0, 1.0; strategy=flag)
        p = pr(y)
    
        @test issetequal(keys(p), -3.0:1/8:1.0 - 1/8)
        @test all(values(p) .≈ 1/2^5)
    end
end

@testset "DistFixedPoint division" begin
    x = DistFixedPoint{5, 2}(0.5)
    y = DistFixedPoint{5, 2}(2.0)
    c = @dice x/y
    q = pr(c)

    for i = -4.0:0.25:4 - 0.25
        for j= -4.0:0.25:4 - 0.25
            x = DistFixedPoint{5, 2}(i)
            y = DistFixedPoint{5, 2}(j)
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

@testset "DistFixedPoint isless" begin
    x = DistFixedPoint{4, 2}(0.75)
    y = DistFixedPoint{4, 2}(-1.75)
    p = pr(x < y)
    @test p[0.0] ≈ 1.0

    x = uniform(DistFixedPoint{3, 1}, 0.0, 1.0)
    y = uniform(DistFixedPoint{3, 1}, 0.0, 1.0)
    p = pr(x < y)
    @test p[1.0] ≈ 0.25

    for i = -2:0.5:1.5
        for j = -2:0.5:1.5
            a = DistFixedPoint{3, 1}(i)
            b = DistFixedPoint{3, 1}(j)
            @test pr(@dice a < b)[i < j] ≈ 1.0
        end
    end

end

@testset "DistFixedPoint exponential" begin
    x = unit_exponential(DistFixedPoint{5, 3}, 1.0)
    @test pr(x)[0.125] ≈ exp(0.125)*(exp(1/8) - 1)/(exp(1) - 1)
    
    x = unit_exponential(DistFixedPoint{10, 9}, -1.0)
    @test pr(x)[0.125] ≈ exp(-0.125)*(exp(-1/2^9) - 1)/(exp(-1) - 1) 
    
    x = exponential(DistFixedPoint{6, 3}, 1.0, 0.0, 2.0)
    pr(x)
    y = unit_exponential(DistFixedPoint{6, 4}, 2.0)
    pr(y)
    @test sum([pr(x)[i] == pr(y)[i/2] for i in 0:0.125:1.875]) == 16 

    x = exponential(DistFixedPoint{6, 3}, 1.0, -1.0, 1.0)
    pr(x)
    @test sum([pr(x)[i] == pr(y)[(i+1)/2] for i in -1:0.125:0.875]) == 16
end

@testset "DistFixedPoint laplace, unit_gamma_one" begin
    x = laplace(DistFixedPoint{10, 3}, 0.0, 1.0, -8.0, 8.0)
    y = exponential(DistFixedPoint{10, 3}, -1.0, 0.0, 8.0)
    @test pr(x)[1]*2 ≈ pr(y)[1]

    actual_dist = Truncated(Laplace(0.0, 1.0), -8.0, 8.0)
    @test pr(x)[0] ≈ cdf(actual_dist, 0.125) - cdf(actual_dist, 0.0)

    # Tests for Gamma distribution (α = 1)
    x = @dice unit_gamma(DistFixedPoint{5, 3}, 0, -1.0)
    a = pr(x)

    d = Truncated(Gamma(1, 1), 0.0, 1.0)
    @test a[0] ≈ (cdf(d, 0.125) - cdf(d, 0))

    x = @dice unit_gamma(DistFixedPoint{5, 3}, 0, -3.0)
    a = pr(x)

    d = Truncated(Gamma(1, 1/3), 0.0, 1.0)
    @test a[0] ≈ (cdf(d, 0.125) - cdf(d, 0))

    # Tests for Gamma distribution for (α = 2)
    x = @dice unit_gamma(DistFixedPoint{5, 3}, 1, -1.0)
    a = pr(x)
    d = Truncated(Gamma(2, 1), 0.0, 1.0)
    @test a[0] ≈ cdf(d, 0.125) - cdf(d, 0)

    x = @dice unit_gamma(DistFixedPoint{5, 3}, 1, -3.0)
    a = pr(x)
    d = Truncated(Gamma(2, 1/3), 0.0, 1.0)
    @test a[0] ≈ cdf(d, 0.125) - cdf(d, 0)

    #Tests for shift_point_gamma
    x = @dice shift_point_gamma(DistFixedPoint{5, 3}, 1, 1.0)
    a = pr(x)
    @test a[0.125]/a[0] ≈ 2exp(0.125)

    x = @dice shift_point_gamma(DistFixedPoint{5, 3}, 2, -2.0)
    a = pr(x)
    @test a[0.125]/a[0] ≈ 4exp(-0.25)

    # Building Gamma(3, 1)





    @vars varint, v2
    function constants(α::Int, β::Float64, ϵ::Float64)
        if α == 0
            []
        else
            c1 = Float64(sympy.Poly(integrate(varint^α*exp(β*varint), (varint, 0, 1)), varint).coeffs().evalf()[1])
            c2 = [Float64(i) for i in sympy.Poly(simplify(v2*integrate(varint^(α-1)*exp(β*varint), (varint, v2, v2 + ϵ))/exp(β*v2)), v2).coeffs()]
            p1 = 0
            for i in eachindex(c2)
                p1 += sum_pgp(β, ϵ, length(c2) + 1 - i) * c2[i]
            end
            p1 /= c1
    
            c2 = [Float64(i) for i in sympy.Poly(simplify(v2*integrate(varint^(α-1) * (varint - v2) *exp(β*varint), (varint, v2, v2 + ϵ))/exp(β*v2)), v2).coeffs()]
            p2 = Vector(undef, α)
            for i in eachindex(c2)
                p2[i] = sum_pgp(β, ϵ, length(c2) - i) * c2[i]
            end
            vcat([p1], p2, constants(α-1, β, ϵ))
        end
    end

    cons = constants(1, -2.0, 0.0625)
    x = @dice unit_gamma(DistFixedPoint{8, 4}, 1, -2.0, constants = cons)
    a = pr(x)[0.0]
    d = Truncated(Gamma(2, 0.5), 0.0, 1.0)
    @test a ≈ cdf(d, 0.0625) - cdf(d, 0.0)
    

    





    #TODO test for beta = 0
    #TODO test for positive beta

end

