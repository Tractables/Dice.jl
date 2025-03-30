using Alea
using Test
using Alea: Flip, num_ir_nodes

@testset "DistInt inference" begin
    x = DistInt{4}([true, false, true, false]) # -6
    @test Alea.bitwidth(x) == 4

    p = pr(x)
    @test p[-5] ≈ 0
    @test p[-6] ≈ 1
    @test p[-7] ≈ 0
   
    x = uniform(DistInt{3})
    p = pr(x)
    @test issetequal(keys(p), -(2^2):(2^2-1))
    @test all(values(p) .≈ 1/2^3)

    x = uniform(DistInt{4}, 3)
    p = pr(x)
    @test x isa DistInt{4}
    @test issetequal(keys(p), 0:(2^3-1))
    @test all(values(p) .≈ 1/2^3)

    @test_throws Exception DistInt{3}([true, false, true, false])
    @test_throws Exception DistInt{5}([true, false, true, false])

    ps1, ps2 = pr(uniform(DistInt{3}), uniform(DistUInt{2}))
    @test issetequal(keys(ps1), -(2^2):(2^2-1))
    @test all(values(ps1) .≈ 1/2^3)

    x = DistInt{4}([true, false, true, false]) # -6
    y = DistInt{4}([false, false, true, true]) # 3
    p = pr(ifelse(flip(0.1), x, y))
    @test p[-6] ≈ 0.1
    @test p[3] ≈ 0.9

    @test prob_equals(x, DistInt{4}(-6))
    @test prob_equals(y, DistInt{4}(3))
end

@testset "DistInt casting" begin
    y = DistInt{4}([flip(0.5), false, true, true])
    z = convert(DistInt{5}, y)
    p1 = pr(z)
    p2 = pr(y)
    @test p1 == p2

    z = convert(DistInt{3}, y)
    p = pr(z)
    @test p[3] ≈ 1.0

    @test pr(@alea convert(DistInt{3}, DistUInt{3}(0)))[0] ≈ 1
    @test pr(@alea convert(DistInt{2}, DistUInt{3}(0)))[0] ≈ 1
    @test pr(@alea convert(DistInt{4}, DistUInt{3}(0)))[0] ≈ 1
    @test pr(@alea convert(DistInt{2}, DistUInt{3}(1)))[1] ≈ 1
    @test pr(@alea convert(DistInt{4}, DistUInt{3}(1)))[1] ≈ 1
    @test pr(@alea convert(DistInt{3}, DistUInt{3}(3)))[3] ≈ 1
    @test_throws ProbException pr(@alea convert(DistInt{3}, DistUInt{3}(4)))
end

@testset "DistInt expectation" begin
    y = DistInt{4}([true, false, true, false])
    @test expectation(y) == -6.0
    @test expectation(@alea y) == -6.0
    @test variance(y) == 0.0
    @test variance(@alea y) == 0.0

    y = DistInt{2}([flip(0.1), flip(0.1)])
    p = pr(y)
    mean = reduce(+, [(key*value) for (key, value) in p])
    @test expectation(y) ≈ mean
    std_sq = reduce(+, [(key*key*value) for (key, value) in p]) - mean^2
    @test variance(y) ≈ std_sq

    x = uniform(DistInt8)
    p = pr(x)
    @test expectation(x) ≈ -0.5
    std_sq = reduce(+, [(key*key*value) for (key, value) in p]) - (-0.5)^2
    @test variance(x) ≈ std_sq
    
    y = prob_equals(x, DistInt8(42))
    @test expectation(x; evidence=y) ≈ 42
    @test variance(x; evidence = y) ≈ 0.0

    y = prob_equals(x, DistInt8(-42))
    @test expectation(x; evidence=y) ≈ -42
    @test variance(x; evidence = y) ≈ 0.0
end

@testset "DistInt triangle" begin
    y = triangle(DistInt{4}, 3)
    p = pr(y)
    n = 2^3
    for i=0:7
        @test p[i] ≈ 2*i/(n*(n-1))
    end
end

@testset "DistInt arithmetic" begin
    a = DistInt{3}(3)
    b = DistInt{3}(3)
    @test_nowarn pr(a + b)
    @test_throws ProbException pr(@alea a + b)

    a = DistInt{3}(-3)
    b = DistInt{3}(-3)
    @test_throws ProbException pr(@alea a + b)

    a = DistInt{3}(-3)
    b = DistInt{3}(3)
    p = pr(a + b)
    @test p[0] == 1

    a = uniform(DistInt{3}, 3)
    b = DistInt{3}(-1)
    @test_throws ProbException p = pr(@alea a + b)

    a = DistInt{3}(3)
    b = DistInt{3}(-2)
    @test_nowarn pr(a - b)
    @test_throws ProbException pr(@alea a - b)

    a = DistInt{3}(-3)
    b = DistInt{3}(2)
    @test_throws ProbException pr(@alea a - b)

    a = DistInt{3}(3)
    b = DistInt{3}(2)
    p = pr(a - b)
    @test p[1] == 1

    a = DistInt{3}(-3)
    b = DistInt{3}(-2)
    p = pr(a - b)
    @test p[-1] == 1

    a = uniform(DistInt{3}, 2)
    b = DistInt{3}(1)
    p = pr(a - b)
    @test issetequal(keys(p), -1:2)
    @test all(values(p) .≈ 1/2^2)

    T = DistInt{2}
    x = uniform(T,1) - T(1)
    y = uniform(T,1) - T(1)
    @test pr(@alea x + y)[-1] ≈ 0.5
    @test pr(x + y)[-1] ≈ 0.5

    # we want overallocation of bits to not affect the computation graph size
    B = 30
    T = DistInt{B}
    x = uniform(T,1) - T(1)
    y = uniform(T,1) - T(1)
    s = convert(DistUInt{B+1}, x.number) + convert(DistUInt{B+1}, y.number)
    @test Alea.num_ir_nodes(s.bits[2]) < 15 
    
    @test pr(@alea -DistInt8(127))[-127] ≈ 1
    @test pr(@alea -DistInt8(-127))[127] ≈ 1
    @test pr(@alea -DistInt8(0))[0] ≈ 1
    @test_throws ProbException pr(@alea -DistInt8(-128))
    
end

@testset "DistInt multiply" begin

    a = DistInt{4}(2)
    b = DistInt{4}(-3)
    p = pr(a*b)
    @test p[-6] ≈ 1

    a = DistInt{4}(-2)
    b = DistInt{4}(-3)
    p = pr(@alea a*b)
    @test p[6] ≈ 1

    a = DistInt{4}(2)
    b = DistInt{4}(3)
    p = pr(a*b)
    @test p[6] ≈ 1

    a = DistInt{4}(-2)
    b = DistInt{4}(3)
    p = pr(a*b)
    @test p[-6] ≈ 1

    a = uniform(DistInt{4}, -2, 2)
    b = uniform(DistInt{4}, -2, 2)
    p = pr(@alea a*b)
    @test p[4] ≈ 1/16
    @test p[0] ≈ 7/16

    for i = -8:7
        for j = -8:7
            a = DistInt{4}(i)
            b = DistInt{4}(j)
            c = @alea a*b
            if (i*j > 7) | (i*j < -8)
                @test_throws ProbException pr(c)
            else
                @test pr(c)[i*j] ≈ 1.0
            end
        end
    end
end

@testset "DistInt uniform" begin
    y = @alea uniform(DistInt{4}, -7, 1)
    p = pr(y)
  
    @test issetequal(keys(p), -7:1:1-1)
    @test all(values(p) .≈ 1/8)

    y = @alea uniform(DistInt{4}, -7, 3)
    p = pr(y)
  
    @test issetequal(keys(p), -7:1:3-1)
    @test all(values(p) .≈ 1/10)

    @test_throws Exception y = uniform(DistInt{4}, -7, 9)

    flags = [:arith]
    map(flags) do flag
        y = @alea uniform(DistInt{4}, -7, 1; strategy=flag)
        p = pr(y)
      
        @test issetequal(keys(p), -7:1:1-1)
        @test all(values(p) .≈ 1/8)
    end

    @test_broken @alea uniform(DistInt{4}, -7, 1; strategy=:ite)
end

@testset "DistInt division" begin
    x = DistInt{4}(7)
    y = DistInt{4}(-3)
    p = pr(@alea x / y)
    @test p[-2] ≈ 1.0

    a = uniform(DistInt{3}, -4, 4)
    b = uniform(DistInt{3}, -4, 4)
    @test_throws ProbException pr(@alea a/b)

    x = DistInt{3}(-4)
    y = DistInt{3}(-4)
    p = pr(@alea x / y)
    @test p[1] ≈ 1.0

    for i = -4:3
        for j = -4:3
            a = DistInt{3}(i)
            b = DistInt{3}(j)
            if (j == 0) | ((i == -4) & (j == -1))
                @test_throws ProbException pr(@alea a/b)
            else
                @test pr(@alea a/b)[i ÷ j] ≈ 1.0
            end
        end
    end
end

@testset "DistInt mod" begin
    x = DistInt{4}(7)
    y = DistInt{4}(-3)
    p = pr(@alea x % y)
    @test p[1] ≈ 1.0

    a = uniform(DistInt{3}, -4, 4)
    b = uniform(DistInt{3}, -4, 4)
    @test_throws ProbException pr(@alea a%b)

    x = DistInt{3}(-4)
    y = DistInt{3}(-4)
    p = pr(@alea x % y)
    @test p[0] ≈ 1.0

    for i = -4:3
        for j = -4:3
            a = DistInt{3}(i)
            b = DistInt{3}(j)
            if (j == 0)
                @test_throws ProbException pr(@alea a%b)
            else
                @test pr(@alea a%b)[i % j] ≈ 1.0
            end
        end
    end
end

@testset "DistInt isless" begin
    x = DistInt{4}(3)
    y = DistInt{4}(-7)
    p = pr(x < y)
    @test p[0.0] ≈ 1.0

    x = uniform(DistInt{3}, 0, 2)
    y = uniform(DistInt{3}, 0, 2)
    p = pr(x < y)
    @test p[1.0] ≈ 0.25

    x = uniform(DistInt{3}, -2, 2)
    y = DistInt{3}(0)
    p = pr(x < y)
    @test p[1] ≈ 1/2

    for i = -4:3
        for j = -4:3
            a = DistInt{3}(i)
            b = DistInt{3}(j)
            @test pr(@alea a < b)[i < j] ≈ 1.0
        end
    end

end

@testset "DistInt unsigned_abs" begin

    x = unsigned_abs(DistInt{8}(3))
    @test x isa DistUInt{8}
    @test pr(x)[3] ≈ 1

    x = unsigned_abs(DistInt{8}(-3))
    @test x isa DistUInt{8}
    @test pr(x)[3] ≈ 1

    x = unsigned_abs(DistInt{8}(0))
    @test x isa DistUInt{8}
    @test pr(x)[0] ≈ 1

    x = unsigned_abs(DistInt{8}(127))
    @test x isa DistUInt{8}
    @test pr(x)[127] ≈ 1

    x = unsigned_abs(DistInt{8}(-128))
    @test x isa DistUInt{8}
    @test pr(x)[128] ≈ 1
    
end
