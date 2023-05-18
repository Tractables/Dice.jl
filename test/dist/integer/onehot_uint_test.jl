using Test
using Dice
using Dice: Flip, num_ir_nodes

@testset "DistUIntOH inference" begin
    x = DistUIntOH{4}([false, false, true, false]) # 2
    @test Dice.bitwidth(x) == 4

    p = pr(x)
    @test p[1] ≈ 0
    @test p[2] ≈ 1
    @test p[3] ≈ 0
   
    x = uniform(DistUIntOH{8})
    p = pr(x)
    @test issetequal(keys(p), 0:(8-1))
    @test all(values(p) .≈ 1/8)

    x = uniform(DistUIntOH{16}, 8)
    p = pr(x)
    @test x isa DistUIntOH{16}
    @test issetequal(keys(p), 0:(2^3-1))
    @test all(values(p) .≈ 1/2^3)

    @test_throws Exception DistUIntOH{3}([false, false, true, false])
    @test_throws Exception DistUIntOH{5}([false, false, true, false])

    ps1, ps2 = pr(uniform(DistUIntOH{8}), uniform(DistUIntOH{4}))
    @test issetequal(keys(ps1), 0:(8-1))
    @test all(values(ps1) .≈ 1/8)
    @test issetequal(keys(ps2), 0:(4-1))
    @test all(values(ps2) .≈ 1/4)

    x = DistUIntOH{16}([false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false]) # 10
    y = DistUIntOH{16}([false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false]) # 3
    p = pr(@dice if flip(0.1) x else y end)
    @test p[10] ≈ 0.1
    @test p[3] ≈ 0.9

    @test prob_equals(x, DistUIntOH{16}(10))
    @test prob_equals(y, DistUIntOH{16}(3))
end

@testset "DistUIntOH operations" begin
    
    x = DistUIntOH{16}([false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false]) # 10
    y = DistUIntOH{16}([false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false]) # 3
    p = pr(x + y)
    @test p[12] ≈ 0
    @test p[13] ≈ 1
    @test p[14] ≈ 0
    p = pr(x - y)
    @test p[6] ≈ 0
    @test p[7] ≈ 1
    @test p[8] ≈ 0

    z = uniform(DistUIntOH{16}, 8)
    y2 = DistUIntOH{16}([false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false]) # 3
    t = z + y
    p = pr(t)
    @test issetequal(keys(p), 3 .+ (0:(8-1)))
    @test all(values(p) .≈ 1/8)
    p = pr((@dice t - y2), ignore_errors=true)
    @test issetequal(keys(p), 1 .+ (0:(8-1)))
    @test all(values(p) .≈ 1/8)

    w = uniform(DistUIntOH{16}, 8)
    p = pr(z + w)
    n = 8
    for i=0:(16-1)
        @test p[i] ≈ (n - abs(i-(n-1)))/n^2
    end

    w = uniform(DistUIntOH{16}, 4)
    z = uniform(DistUIntOH{16}, 4)
    p = pr((@dice w + y - z), ignore_errors=true)
    n = 4
    for i=0:6
        @test p[i] ≈ (n - abs(i-(n-1)))/n^2
    end

    # @test_throws Exception pr(uniform(DistUIntOH{3}, 3) + uniform(DistUIntOH{3}, 3))
    # @test_throws Exception pr(@dice uniform(DistUIntOH{3}, 3) + uniform(DistUIntOH{3}, 3))

    # @test_throws Exception pr(uniform(DistUIntOH{3}, 3) - uniform(DistUIntOH{3}, 3))
    # @test_throws Exception pr(@dice uniform(DistUIntOH{3}, 3) - uniform(DistUIntOH{3}, 3))
    
    x = uniform(DistUIntOH{8}, 4) # uniform(0, 4)
    y = uniform(DistUIntOH{8}, 4)
    p = pr(prob_equals(x, y))
    @test p[1] ≈ 4/16

    x = uniform(DistUIntOH{8}, 4) # uniform(0, 4)
    y = uniform(DistUIntOH{8}, 4)
    p = pr(x < y)
    @test p[1] ≈ 6/16

end

# @testset "DistUIntOH casting" begin
#     y = DistUIntOH{4}([false, false, true, true]) # 3
#     z = convert(y, DistUIntOH{3})
#     p = pr(z)
#     @test p[2] ≈ 0
#     @test p[3] ≈ 1
#     @test p[4] ≈ 0

#     y = DistUIntOH{4}([flip(0.5), false, true, true]) # 3
#     code = @dice convert(y, DistUIntOH{3})
#     @test_throws Exception pr(code)

#     y = DistUIntOH{4}([false, false, true, flip(0.5)]) # 3
#     z = convert(y, DistUIntOH{5})
#     @test typeof(z) == DistUIntOH{5}
#     p = pr(y)
#     @test p[2] ≈ 0.5
#     @test p[3] ≈ 0.5
# end

# @testset "DistUIntOH moments" begin
#     y = DistUIntOH{4}([true, false, true, false])
#     @test expectation(y) == 10.0
#     @test variance(y) == 0.0

#     y = DistUIntOH{2}([flip(0.1), flip(0.1)])
#     p = pr(y)
#     mean = reduce(+, [(key*value) for (key, value) in p])
#     @test expectation(y) ≈ mean
#     std_sq = reduce(+, [(key*key*value) for (key, value) in p]) - mean^2
#     @test variance(y) ≈ std_sq

#     x = uniform(DistUIntOH8)
#     p = pr(x)
#     @test expectation(x) ≈ (2^8-1)/2
#     std_sq = reduce(+, [(key*key*value) for (key, value) in p]) - ((2^8-1)/2)^2
#     @test variance(x) ≈ std_sq
#     y = prob_equals(x, DistUIntOH8(42))
#     @test expectation(x; evidence=y) ≈ 42
#     @test variance(x; evidence=y) ≈ 0.0
# end

# @testset "DistUIntOH casting" begin
#     y = DistUIntOH{4}([false, false, true, true]) # 3
#     z = convert(y, DistUIntOH{3})
#     p = pr(z)
#     @test p[2] ≈ 0
#     @test p[3] ≈ 1
#     @test p[4] ≈ 0

#     y = DistUIntOH{4}([flip(0.5), false, true, true]) # 3
#     code = @dice convert(y, DistUIntOH{3})
#     @test_throws Exception pr(code)

#     y = DistUIntOH{4}([false, false, true, flip(0.5)]) # 3
#     z = convert(y, DistUIntOH{5})
#     @test typeof(z) == DistUIntOH{5}
#     p = pr(y)
#     @test p[2] ≈ 0.5
#     @test p[3] ≈ 0.5
# end

@testset "DistUIntOH expectation" begin
    y = DistUIntOH{4}([false, false, true, false])
    @test expectation(y) == 2.0
    @test expectation(@dice y) == 2.0

    y = uniform(DistUIntOH{8}, 0, 7)
    p = pr(y)
    mean = reduce(+, [(key*value) for (key, value) in p])
    @test expectation(y) ≈ mean
end

@testset "DistUIntOH uniform" begin

    x = uniform(DistUIntOH{8}, 0, 7)
    p = pr(x)
    for i=0:6
        @test p[i] ≈ 1/7
    end
    @test p[7] ≈ 0
    
    @test_throws Exception uniform(DistUIntOH{8}, 0, 10)
    @test_throws Exception uniform(DistUIntOH{8}, -1, 7)
    @test_throws Exception uniform(DistUIntOH{8}, 4, 3)
    @test_throws Exception uniform(DistUIntOH{8}, 3, 3)

    x = uniform(DistUIntOH{8}, 3, 4)
    p = pr(x)
    @test p[3] ≈ 1

    x = uniform(DistUIntOH{32}, 3, 17)
    p = pr(x)
    for i=3:16
        @test p[i] ≈ 1/14
    end
    y = DistUIntOH{32}(10)
    p = pr(x < y)
    @test p[1] ≈ 7/14

    z = DistUIntOH{32}(0)
    p = pr(prob_equals(x, z))
    @test p[1] ≈ 0

end

@testset "DistUIntOH and discrete" begin
    a = discrete(DistUIntOH{4}, [0.1, 0.2, 0.3, 0.4])
    p = pr(a)
    for i=0:3
        @test p[i] ≈ (i+1)/10
    end 
end

#TODO: better unit tests for multiplication maybe
@testset "DistUIntOH multiplication" begin
    x = DistUIntOH{16}(3)
    y = DistUIntOH{16}(5)
    p = pr(x*y)
    @test p[15] ≈ 1.0

    x = DistUIntOH{16}(3)
    y = DistUIntOH{16}(2)
    p = pr(x*y)
    @test p[6] ≈ 1.0

    # x = DistUIntOH{16}(3)
    # y = DistUIntOH{16}(6)
    # @test_throws Exception p = pr(x*y)

    x = uniform(DistUIntOH{16}, 4)
    y = uniform(DistUIntOH{16}, 4)
    p = pr(@dice y*x)
    @test p[0] ≈ 7/16
    @test p[9] ≈ 1/16
end

@testset "DistUIntOH division" begin
    x = DistUIntOH{16}(15)
    y = DistUIntOH{16}(3)
    p = pr(@dice x / y)
    @test p[5] ≈ 1.0

    a = uniform(DistUIntOH{8}, 0, 8)
    b = uniform(DistUIntOH{8}, 0, 8)
    c = @dice a/b
    @test_throws ProbException pr(c)

    code = @dice begin
            a = uniform(DistUIntOH{8}, 1, 8)
            b = uniform(DistUIntOH{8}, 1, 8)
            c = a/b
            c
    end
    p = pr(code)
    @test p[0.0] ≈ 21/49
    @test p[5.0] ≈ 1/49

    for i = 1:7
        for j = 1:7
            a = DistUIntOH{8}(i)
            b = DistUIntOH{8}(j)
            c = pr(@dice a/b)
            @test c[floor(i/j)] ≈ 1.0
        end
    end
end

@testset "DistUIntOH mod" begin
    x = DistUIntOH{16}(15)
    y = DistUIntOH{16}(3)
    p = pr(@dice x % y)
    @test p[0] ≈ 1.0

    a = uniform(DistUIntOH{8}, 0, 8)
    b = uniform(DistUIntOH{8}, 0, 8)
    c = @dice a%b
    @test_throws ProbException pr(c)

    code = @dice begin
            a = uniform(DistUIntOH{8}, 1, 8)
            b = uniform(DistUIntOH{8}, 1, 8)
            c = a%b
            c
    end
    p = pr(code)
    @test p[0.0] ≈ 16/49
    @test p[5.0] ≈ 2/49

    for i = 1:7
        for j = 1:7
            a = DistUIntOH{8}(i)
            b = DistUIntOH{8}(j)
            c = pr(@dice a%b)
            @test c[floor(i%j)] ≈ 1.0
        end
    end
end