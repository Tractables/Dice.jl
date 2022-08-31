using Test
using Dice
using Dice: Flip, ifelse, num_ir_nodes

@testset "DistInt inference" begin
    x = DistInt{4}([true, false, true, false]) # 10
    @test Dice.bitwidth(x) == 4

    p = pr(x)
    @test p[9] ≈ 0
    @test p[10] ≈ 1
    @test p[11] ≈ 0
   
    x = uniform(DistInt{3})
    p = pr(x)
    @test issetequal(keys(p), 0:(2^3-1))
    @test all(values(p) .≈ 1/2^3)

    x = uniform(DistInt{4}, 3)
    p = pr(x)
    @test x isa DistInt{4}
    @test issetequal(keys(p), 0:(2^3-1))
    @test all(values(p) .≈ 1/2^3)

    x = DistInt([true, false, true, false])
    @test Dice.bitwidth(x) == 4

    @test_throws Exception DistInt{3}([true, false, true, false])
    @test_throws Exception DistInt{5}([true, false, true, false])

    ps1, ps2 = pr(uniform(DistInt{3}), uniform(DistInt{2}))
    @test issetequal(keys(ps1), 0:(2^3-1))
    @test all(values(ps1) .≈ 1/2^3)
    @test issetequal(keys(ps2), 0:(2^2-1))
    @test all(values(ps2) .≈ 1/2^2)

    x = DistInt{4}([true, false, true, false]) # 10
    y = DistInt{4}([false, false, true, true]) # 3
    p = pr(@dice if flip(0.1) x else y end)
    @test p[10] ≈ 0.1
    @test p[3] ≈ 0.9

    @test prob_equals(x, DistInt{4}(10))
    @test prob_equals(y, DistInt{4}(3))
end

@testset "DistInt operations" begin
    
    x = DistInt{4}([true, false, true, false]) # 10
    y = DistInt{4}([false, false, true, true]) # 3
    p = pr(x + y)
    @test p[12] ≈ 0
    @test p[13] ≈ 1
    @test p[14] ≈ 0
    p = pr(x - y)
    @test p[6] ≈ 0
    @test p[7] ≈ 1
    @test p[8] ≈ 0

    z = uniform(DistInt{4}, 3)
    y2 = DistInt{4}([false, false, true, false])
    t = z + y
    p = pr(t)
    @test issetequal(keys(p), 3 .+ (0:(2^3-1)))
    @test all(values(p) .≈ 1/2^3)
    p = pr((@dice t - y2), ignore_errors=true)
    @test issetequal(keys(p), 1 .+ (0:(2^3-1)))
    @test all(values(p) .≈ 1/2^3)

    w = uniform(DistInt{4}, 3)
    p = pr(z + w)
    n = 2^3
    for i=0:(2^4-1)
        @test p[i] ≈ (n - abs(i-(n-1)))/n^2
    end

    w = uniform(DistInt{4}, 2)
    z = uniform(DistInt{4}, 2)
    p = pr((@dice w + y - z), ignore_errors=true)
    n = 2^2
    for i=0:6
        @test p[i] ≈ (n - abs(i-(n-1)))/n^2
    end

    @test_throws Exception pr(uniform(DistInt{3}, 3)+uniform(DistInt{3}, 3))
    @test_throws Exception pr(@dice uniform(DistInt{3}, 3) + uniform(DistInt{3}, 3))

    x = DistInt{3}([false, flip(0.5), flip(0.5)]) # uniform(0, 4)
    y = DistInt{3}([false, flip(0.5), flip(0.5)])
    p = pr(prob_equals(x, y))
    @test p[1] ≈ 4/16

    x = DistInt{3}([false, flip(0.5), flip(0.5)]) # uniform(0, 4)
    y = DistInt{3}([false, flip(0.5), flip(0.5)])
    p = pr(x < y)
    @test p[1] ≈ 6/16

    @test_throws Exception pr(uniform(DistInt{3}, 3)-uniform(DistInt{3}, 3))
    @test_throws Exception pr(@dice uniform(DistInt{3}, 3) - uniform(DistInt{3}, 3))

end

@testset "DistInt casting" begin
    y = DistInt{4}([false, false, true, true]) # 3
    z = convert(y, DistInt{3})
    p = pr(z)
    @test p[2] ≈ 0
    @test p[3] ≈ 1
    @test p[4] ≈ 0

    y = DistInt{4}([flip(0.5), false, true, true]) # 3
    code = @dice convert(y, DistInt{3})
    @test_throws Exception pr(code)

    y = DistInt{4}([false, false, true, flip(0.5)]) # 3
    z = convert(y, DistInt{5})
    @test typeof(z) == DistInt{5}
    p = pr(y)
    @test p[2] ≈ 0.5
    @test p[3] ≈ 0.5
end

@testset "DistInt expectation" begin
    y = DistInt{4}([true, false, true, false])
    @test expectation(y) == 10.0

    y = DistInt{2}([flip(0.1), flip(0.1)])
    p = pr(y)
    mean = reduce(+, [(key*value) for (key, value) in p])
    @test expectation(y) ≈ mean
end

@testset "DistInt uniform" begin
    uniform_funcs = [uniform_arith, uniform_ite]

    map(uniform_funcs) do uniform 
        x = uniform(DistInt{3}, 0, 7)
        p = pr(x)
        for i=0:6
            @test p[i] ≈ 1/7
        end
        @test p[7] ≈ 0
        
        @test_throws Exception uniform(DistInt{3}, 0, 10)
        @test_throws Exception uniform(DistInt{3}, -1, 7)
        @test_throws Exception uniform(DistInt{3}, 4, 3)
        @test_throws Exception uniform(DistInt{3}, 3, 3)

        x = uniform(DistInt{3}, 3, 4)
        p = pr(x)
        @test p[3] ≈ 1

        x = uniform(DistInt{5}, 3, 17)
        p = pr(x)
        for i=3:16
            @test p[i] ≈ 1/14
        end
        y = DistInt{5}(10)
        p = pr(x < y)
        @test p[1] ≈ 7/14

        z = DistInt{5}(0)
        p = pr(prob_equals(x, z))
        @test p[1] ≈ 0

    end
end

@testset "DistInt triangle and discrete" begin
    x = triangle(DistInt{4}, 3)
    p = pr(x)
    n = 2^3
    for i=0:7
        @test p[i] ≈ 2*i/(n*(n-1))
    end

    a = discrete(DistInt{3}, [0.1, 0.2, 0.3, 0.4])
    p = pr(a)
    for i=0:3
        @test p[i] ≈ (i+1)/10
    end 
end
