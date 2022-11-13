using Test
using Dice

@testset "DistString core" begin
    cg = @dice begin
        s = if flip(3/5) DistString("sand") else DistString("san") end
        if flip(2/3) s + 'd' else s end
    end
    dist = pr(cg)
    @test dist["sand"] ≈ 3/5 * 1/3 + 2/5 * 2/3
    @test dist["sandd"] ≈ 3/5 * 2/3
    @test dist["san"] ≈ 2/5 * 1/3

    # Test concatenation, appending, ifelse
    cg = @dice begin
        s = if flip(3/5) DistString("sand") else DistString("san") end
        s = if flip(2/3) s + 'd' else s end
        t = if flip(1/10) DistString("wich") else DistString("box") end
        s + t
    end

    dist = pr(cg)
    @test sum(values(dist)) ≈ 1
    @test dist["sandwich"] ≈ 7/150
    @test dist["sandbox"] ≈ 21/50
    @test dist["sanwich"] ≈ 1/75
    @test dist["sanbox"] ≈ 3/25
    @test dist["sanddwich"] ≈ 1/25
    @test dist["sanddbox"] ≈ 9/25

    # Test concatenation for empty strings
    cg = DistString("") + DistString("")
    dist = pr(cg)
    @test sum(values(dist)) ≈ 1
    @test dist[""] ≈ 1


    # Test getindex, setindex
    cg = @dice begin
        s = if flip(0.6) DistString("abc") else DistString("xyz") end

        # Choose whether to change index 1 (Pr=0.3) or 2 (Pr = 0.7)
        i = if flip(0.3) DistUInt32(1) else DistUInt32(2) end

        c = if flip(0.1) DistChar('d') else DistChar('e') end
        s = prob_setindex(s, i, c)
        prob_equals(DistString("aec"), s)
    end
    @test pr(cg)[true] ≈ 0.6*0.7*0.9

    # Test lessthan
    cg = @dice begin
        s = if flip(0.6) DistString("abc") else DistString("xyz") end
        t = if flip(0.6) DistString("abc") else DistString("xyz") end
        s < t
    end
    @test pr(cg)[true] ≈ 0.6 * 0.4


    # Test lessthan for identical strings
    cg = @dice begin
        DistString("abc") < DistString("abc")
    end
    @test pr(cg)[true] ≈ 0


    # Test lessthan for strings that differ only in length
    cg = @dice begin
        DistString("abc") < DistString("abca")
    end
    @test pr(cg)[true] ≈ 1
    cg = @dice begin
        DistString("abca") < DistString("abc")
    end
    @test pr(cg)[true] ≈ 0

    # Test leq, geq
    @test pr(DistString("abc") <= DistString("abc"))[true] == 1
    @test pr(DistString("abc") >= DistString("abc"))[true] == 1
    @test pr(DistString("abcd") <= DistString("abc"))[true] == 0
    @test pr("abc" <= DistString("abc"))[true] == 1
    @test pr(DistString("abc") >= "abc")[true] == 1
    @test pr("abcd" <= DistString("abc"))[true] == 0

    # Test that case where multiple bit assignments represent the same string
    # is handled properly
    cg = @dice begin
        chars = [
            DistChar('a'),
            DistChar('b'),
            if flip(.3) DistChar('c') else DistChar('d') end
        ]
        DistString(chars, DistUInt32(2))
    end
    dist = pr(cg)
    @test length(dist) == 1
    @test dist["ab"] == 1
end
