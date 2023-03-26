using Test
using Dice
using Dice: Flip, num_ir_nodes

@testset "DistUInt inference" begin
    x = DistUInt{4}([true, false, true, false]) # 10
    @test Dice.bitwidth(x) == 4

    p = pr(x)
    @test p[9] ≈ 0
    @test p[10] ≈ 1
    @test p[11] ≈ 0
   
    x = uniform(DistUInt{3})
    p = pr(x)
    @test issetequal(keys(p), 0:(2^3-1))
    @test all(values(p) .≈ 1/2^3)

    x = uniform(DistUInt{4}, 3)
    p = pr(x)
    @test x isa DistUInt{4}
    @test issetequal(keys(p), 0:(2^3-1))
    @test all(values(p) .≈ 1/2^3)

    x = DistUInt([true, false, true, false])
    @test Dice.bitwidth(x) == 4

    @test_throws Exception DistUInt{3}([true, false, true, false])
    @test_throws Exception DistUInt{5}([true, false, true, false])

    ps1, ps2 = pr(uniform(DistUInt{3}), uniform(DistUInt{2}))
    @test issetequal(keys(ps1), 0:(2^3-1))
    @test all(values(ps1) .≈ 1/2^3)
    @test issetequal(keys(ps2), 0:(2^2-1))
    @test all(values(ps2) .≈ 1/2^2)

    x = DistUInt{4}([true, false, true, false]) # 10
    y = DistUInt{4}([false, false, true, true]) # 3
    p = pr(@dice if flip(0.1) x else y end)
    @test p[10] ≈ 0.1
    @test p[3] ≈ 0.9

    @test prob_equals(x, DistUInt{4}(10))
    @test prob_equals(y, DistUInt{4}(3))
end

@testset "DistUInt operations" begin
    
    x = DistUInt{4}([true, false, true, false]) # 10
    y = DistUInt{4}([false, false, true, true]) # 3
    p = pr(x + y)
    @test p[12] ≈ 0
    @test p[13] ≈ 1
    @test p[14] ≈ 0
    p = pr(x - y)
    @test p[6] ≈ 0
    @test p[7] ≈ 1
    @test p[8] ≈ 0

    z = uniform(DistUInt{4}, 3)
    y2 = DistUInt{4}([false, false, true, false])
    t = z + y
    p = pr(t)
    @test issetequal(keys(p), 3 .+ (0:(2^3-1)))
    @test all(values(p) .≈ 1/2^3)
    p = pr((@dice t - y2), ignore_errors=true)
    @test issetequal(keys(p), 1 .+ (0:(2^3-1)))
    @test all(values(p) .≈ 1/2^3)

    w = uniform(DistUInt{4}, 3)
    p = pr(z + w)
    n = 2^3
    for i=0:(2^4-1)
        @test p[i] ≈ (n - abs(i-(n-1)))/n^2
    end

    w = uniform(DistUInt{4}, 2)
    z = uniform(DistUInt{4}, 2)
    p = pr((@dice w + y - z), ignore_errors=true)
    n = 2^2
    for i=0:6
        @test p[i] ≈ (n - abs(i-(n-1)))/n^2
    end

    @test_nowarn pr(uniform(DistUInt{3}, 3) + uniform(DistUInt{3}, 3)) # currently the default is no error checking outside of dynamo
    @test_throws Exception pr(@dice uniform(DistUInt{3}, 3) + uniform(DistUInt{3}, 3))

    @test_nowarn pr(uniform(DistUInt{3}, 3) - uniform(DistUInt{3}, 3)) # currently the default is no error checking outside of dynamo
    @test_throws Exception pr(@dice uniform(DistUInt{3}, 3) - uniform(DistUInt{3}, 3))
    
    x = DistUInt{3}([false, flip(0.5), flip(0.5)]) # uniform(0, 4)
    y = DistUInt{3}([false, flip(0.5), flip(0.5)])
    p = pr(prob_equals(x, y))
    @test p[1] ≈ 4/16

    x = DistUInt{3}([false, flip(0.5), flip(0.5)]) # uniform(0, 4)
    y = DistUInt{3}([false, flip(0.5), flip(0.5)])
    p = pr(x < y)
    @test p[1] ≈ 6/16

end

@testset "DistUInt casting" begin
    y = DistUInt{4}([false, false, true, true]) # 3
    z = convert(DistUInt{3}, y)
    p = pr(z)
    @test p[2] ≈ 0
    @test p[3] ≈ 1
    @test p[4] ≈ 0

    y = DistUInt{4}([flip(0.5), false, true, true]) # 3
    code = @dice convert(DistUInt{3}, y)
    @test_throws Exception pr(code)

    y = DistUInt{4}([false, false, true, flip(0.5)]) # 3
    z = convert(DistUInt{5}, y)
    @test typeof(z) == DistUInt{5}
    p = pr(y)
    @test p[2] ≈ 0.5
    @test p[3] ≈ 0.5
end

@testset "DistUInt moments" begin
    y = DistUInt{4}([true, false, true, false])
    @test expectation(y) == 10.0
    @test variance(y) == 0.0

    y = DistUInt{2}([flip(0.1), flip(0.1)])
    p = pr(y)
    mean = reduce(+, [(key*value) for (key, value) in p])
    @test expectation(y) ≈ mean
    std_sq = reduce(+, [(key*key*value) for (key, value) in p]) - mean^2
    @test variance(y) ≈ std_sq

    x = uniform(DistUInt8)
    p = pr(x)
    @test expectation(x) ≈ (2^8-1)/2
    std_sq = reduce(+, [(key*key*value) for (key, value) in p]) - ((2^8-1)/2)^2
    @test variance(x) ≈ std_sq
    y = prob_equals(x, DistUInt8(42))
    @test expectation(x; evidence=y) ≈ 42
    @test variance(x; evidence=y) ≈ 0.0
end

@testset "DistUInt casting" begin
    y = DistUInt{4}([false, false, true, true]) # 3
    z = convert(DistUInt{3}, y)
    p = pr(z)
    @test p[2] ≈ 0
    @test p[3] ≈ 1
    @test p[4] ≈ 0
    @test_nowarn convert(DistUInt{3}, y)

    y = DistUInt{4}([flip(0.5), false, true, true]) # 3
    code = @dice convert(DistUInt{3}, y)
    @test_throws ProbException pr(code)

    y = DistUInt{4}([false, false, true, flip(0.5)]) # 3
    z = convert(DistUInt{5}, y)
    @test typeof(z) == DistUInt{5}
    p = pr(y)
    @test p[2] ≈ 0.5
    @test p[3] ≈ 0.5

    x = DistUInt{4}([false, flip(0.5), true, true])
    @test_throws ProbException pr(@dice convert(DistUInt{2}, x))
end

@testset "DistUInt expectation" begin
    y = DistUInt{4}([true, false, true, false])
    @test expectation(y) == 10.0
    @test expectation(@dice y) == 10.0

    y = DistUInt{2}([flip(0.1), flip(0.1)])
    p = pr(y)
    mean = reduce(+, [(key*value) for (key, value) in p])
    @test expectation(y) ≈ mean
end

@testset "DistUInt uniform" begin
    uniform_funcs = [uniform_arith, uniform_ite]

    map(uniform_funcs) do uniform 
        x = uniform(DistUInt{3}, 0, 7)
        p = pr(x)
        for i=0:6
            @test p[i] ≈ 1/7
        end
        @test p[7] ≈ 0
        
        @test_throws Exception uniform(DistUInt{3}, 0, 10)
        @test_throws Exception uniform(DistUInt{3}, -1, 7)
        @test_throws Exception uniform(DistUInt{3}, 4, 3)
        @test_throws Exception uniform(DistUInt{3}, 3, 3)

        x = uniform(DistUInt{3}, 3, 4)
        p = pr(x)
        @test p[3] ≈ 1

        x = uniform(DistUInt{5}, 3, 17)
        p = pr(x)
        for i=3:16
            @test p[i] ≈ 1/14
        end
        y = DistUInt{5}(10)
        p = pr(x < y)
        @test p[1] ≈ 7/14

        z = DistUInt{5}(0)
        p = pr(prob_equals(x, z))
        @test p[1] ≈ 0

    end
    
    flags = [:ite, :arith]
    map(flags) do flag
        x = uniform(DistUInt{3}, 0, 7; strategy=flag)
        p = pr(x)
        for i=0:6
            @test p[i] ≈ 1/7
        end
        @test p[7] ≈ 0
    end
end

@testset "DistUInt triangle and discrete" begin
    x = triangle(DistUInt{4}, 3)
    p = pr(x)
    n = 2^3
    for i=0:7
        @test p[i] ≈ 2*i/(n*(n-1))
    end

    a = discrete(DistUInt{3}, [0.1, 0.2, 0.3, 0.4])
    p = pr(a)
    for i=0:3
        @test p[i] ≈ (i+1)/10
    end 
end

#TODO: better unit tests for multiplication maybe
@testset "DistUInt multiplication" begin
    x = DistUInt{4}(3)
    y = DistUInt{4}(5)
    p = pr(x*y)
    @test p[15] ≈ 1.0

    x = DistUInt{4}(3)
    y = DistUInt{4}(2)
    p = pr(x*y)
    @test p[6] ≈ 1.0

    x = DistUInt{4}(3)
    y = DistUInt{4}(6)
    @test_throws Exception p = pr(@dice x*y)

    x = uniform(DistUInt{4}, 2)
    y = uniform(DistUInt{4}, 2)
    p = pr(@dice y*x)
    @test p[0] ≈ 7/16
    @test p[9] ≈ 1/16
end

@testset "DistUInt division" begin
    x = DistUInt{4}(15)
    y = DistUInt{4}(3)
    p = pr(@dice x / y)
    @test p[5] ≈ 1.0

    a = uniform_arith(DistUInt{3}, 0, 8)
    b = uniform_arith(DistUInt{3}, 0, 8)
    c = @dice a/b
    @test_throws ProbException pr(c)

    code = @dice begin
            a = uniform_arith(DistUInt{3}, 1, 8)
            b = uniform_arith(DistUInt{3}, 1, 8)
            c = a/b
            c
    end
    p = pr(code)
    @test p[0.0] ≈ 21/49
    @test p[5.0] ≈ 1/49

    for i = 1:7
        for j = 1:7
            a = DistUInt{3}(i)
            b = DistUInt{3}(j)
            c = pr(@dice a/b)
            @test c[floor(i/j)] ≈ 1.0
        end
    end
end

@testset "DistUInt mod" begin
    x = DistUInt{4}(15)
    y = DistUInt{4}(3)
    p = pr(@dice x % y)
    @test p[0] ≈ 1.0

    a = uniform_arith(DistUInt{3}, 0, 8)
    b = uniform_arith(DistUInt{3}, 0, 8)
    c = @dice a%b
    @test_throws ProbException pr(c)

    code = @dice begin
            a = uniform_arith(DistUInt{3}, 1, 8)
            b = uniform_arith(DistUInt{3}, 1, 8)
            c = a%b
            c
    end
    p = pr(code)
    @test p[0.0] ≈ 16/49
    @test p[5.0] ≈ 2/49

    for i = 1:7
        for j = 1:7
            a = DistUInt{3}(i)
            b = DistUInt{3}(j)
            c = pr(@dice a%b)
            @test c[floor(i%j)] ≈ 1.0
        end
    end
end