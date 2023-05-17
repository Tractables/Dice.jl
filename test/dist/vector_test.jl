using Test
using Dice

@testset "DistVector core" begin
    # Test concatenation, appending, ifelse
    cg = @dice_ite begin
        v = if flip(3/5)
            DistVector([DistUInt32(1),DistUInt32(2),DistUInt32(3),DistUInt32(4)])
        else
            DistVector([DistUInt32(7),DistUInt32(6),DistUInt32(5)])
        end
        v = if flip(2/3) prob_append(v, DistUInt32(100)) else v end
        v2 = if flip(1/10)
            DistVector([DistUInt32(333), DistUInt32(444)])
        else
            DistVector([DistUInt32(555)])
        end
        prob_extend(v, v2)
    end
    dist = pr(cg)
    @test sum(values(dist)) ≈ 1
    @test dist[[1, 2, 3, 4, 100, 333, 444]] ≈ 3/5 * 2/3 * 1/10
    @test dist[[1, 2, 3, 4, 100, 555]] ≈ 3/5 * 2/3 * 9/10
    @test dist[[1, 2, 3, 4, 333, 444]] ≈ 3/5 * 1/3 * 1/10
    @test dist[[1, 2, 3, 4, 555]] ≈ 3/5 * 1/3 * 9/10
    @test dist[[7, 6, 5, 100, 333, 444]] ≈ 2/5 * 2/3 * 1/10
    @test dist[[7, 6, 5, 100, 555]] ≈ 2/5 * 2/3 * 9/10
    @test dist[[7, 6, 5, 333, 444]] ≈ 2/5 * 1/3 * 1/10
    @test dist[[7, 6, 5, 555]] ≈ 2/5 * 1/3 * 9/10

    cg = @dice_ite begin
        v1 = DistVector{DistInt32}()
        v2 = ifelse(flip(1/2), prob_append(v1, DistInt32(6)), v1)
        v3 = ifelse(flip(1/2), prob_append(v2, DistInt32(7)), v2)
        ifelse(flip(1/2), prob_append(v3, DistInt32(6)), v3)
    end
    dist = pr(cg)
    @test length(dist) == 7
    @test dist[[]] ≈ 1/8
    @test dist[[7]] ≈ 1/8
    @test dist[[6]] ≈ 1/4
    @test dist[[6, 6]] ≈ 1/8
    @test dist[[6, 7]] ≈ 1/8
    @test dist[[7, 6]] ≈ 1/8
    @test dist[[6, 7, 6]] ≈ 1/8
    
    
    # Test concatenation for empty vectors
    cg = @dice_ite begin
        prob_extend(DistVector{DistUInt32}(), DistVector{DistUInt32}())
    end
    dist = pr(cg)
    @test sum(values(dist)) ≈ 1
    @test dist[[]] ≈ 1
    
    
    cg = @dice_ite begin
        prob_extend(DistVector{DistString}(Vector{DistString}()), DistVector([DistString("hi")]))
    end
    dist = pr(cg)
    @test sum(values(dist)) ≈ 1
    @test dist[["hi"]] ≈ 1
    
    
    # Test getindex, setindex
    cg = @dice_ite begin
        s = if flip(0.6)
            DistVector(Vector{AnyBool}([flip(0), flip(0), flip(0)]))
        else
            DistVector(Vector{AnyBool}([flip(1), flip(1)]))
        end
        
        # Choose whether to change index 1 (Pr=0.3) or 2 (Pr = 0.7)
        i = if flip(0.3) DistUInt32(1) else DistUInt32(2) end
        
        # Choose new value
        c = if flip(0.1) flip(0) else flip(1) end

        s = prob_setindex(s, i, c)

        # Must choose the first vector, and set index 2 to true
        prob_equals(DistVector([flip(0), flip(1), flip(0)]), s)
    end
    dist = pr(cg)
    @test dist[true] ≈ 0.6*0.7*0.9
    
    # Test prob_startswith
    cg = @dice_ite begin
        s = DistVector(AnyBool[flip(0), flip(0.3), flip(0)])
        t = DistVector(AnyBool[flip(0), flip(1)])
        prob_startswith(s, t)
    end
    @test pr(cg)[true] ≈ 0.3

    cg = @dice_ite begin
        s = if flip(0.3)
            DistVector(AnyBool[false, true, false])
        else
            DistVector(AnyBool[])
        end
        t = DistVector(AnyBool[false, true])
        prob_startswith(s, t)
    end
    @test pr(cg)[true] ≈ 0.3
    
    cg = @dice_ite begin
        s = DistVector(AnyBool[flip(0)])
        s = if flip(0.3) s else prob_append(s, flip(0.4)) end
        t = DistVector(AnyBool[flip(0.9), flip(1)])
        prob_startswith(s, t)
    end
    @test pr(cg)[true] ≈ 0.1 * 0.7 * 0.4
    
    # Test prob_contains
    _5, _6, _7, _8 = DistInt32(5), DistInt32(6), DistInt32(7), DistInt32(8)
    
    cg = @dice_ite begin
        s = DistVector([_5, _6, _7])
        if flip(0.3)
            prob_append(s, _8)
        else
            s
        end
        prob_contains(s, _5) & prob_contains(s, _6) & prob_contains(s, _7) & !prob_contains(s, _8)
    end
    @test pr(cg)[true] == 1

    cg = @dice_ite begin
        s = DistVector([_5, _6, _7])
        t = if flip(0.3)
            prob_append(s, _8)
        else
            s
        end
        prob_contains(t, _8)
    end
    @test pr(cg)[true] == 0.3

    # Test sort

    cg = @dice_ite begin
        s = DistVector([_6, _5])
        sort(s)
    end
    dist = pr(cg)
    @test length(dist) == 1
    @test dist[[5, 6]] == 1

    cg = @dice_ite begin
        s = DistVector([_8, ifelse(flip(2/3), _5, _7)])
        t = ifelse(flip(3/10), prob_append(s, _6), s)
        sort(t)
    end
    dist = pr(cg)
    @test length(dist) == 4
    @test dist[[5, 6, 8]] ≈ 3/10 * 2/3
    @test dist[[6, 7, 8]] ≈ 3/10 * 1/3
    @test dist[[5, 8]] ≈ 7/10 * 2/3
    @test dist[[7, 8]] ≈ 7/10 * 1/3

    cg = @dice_ite begin
        v1 = DistVector{DistInt32}()
        v2 = ifelse(flip(1/2), prob_append(v1, _8), v1)
        v3 = ifelse(flip(1/2), prob_append(v2, _7), v2)
        v4 = ifelse(flip(1/2), prob_append(v3, _6), v3)
        sort(v4)
    end
    dist = pr(cg)
    @test length(dist) == 8
    @test dist[[]] ≈ 1/8
    @test dist[[7]] ≈ 1/8
    @test dist[[6]] ≈ 1/8
    @test dist[[8]] ≈ 1/8
    @test dist[[6, 8]] ≈ 1/8
    @test dist[[6, 7]] ≈ 1/8
    @test dist[[7, 8]] ≈ 1/8
    @test dist[[6, 7, 8]] ≈ 1/8

    cg = sort(DistVector{DistInt32}())
    dist = pr(cg)
    @test length(dist) == 1
    @test dist[[]] == 1

    cg = @dice_ite begin
        v1 = DistVector{DistInt32}()
        v2 = ifelse(flip(1/2), prob_append(v1, _6), v1)
        v3 = ifelse(flip(1/2), prob_append(v2, _7), v2)
        v4 = ifelse(flip(1/2), prob_append(v3, _6), v3)
        sort(v4)
    end
    dist = pr(cg)
    @test length(dist) == 6
    @test dist[[]] ≈ 1/8
    @test dist[[7]] ≈ 1/8
    @test dist[[6]] ≈ 1/4
    @test dist[[6, 6]] ≈ 1/8
    @test dist[[6, 7]] ≈ 1/4
    @test dist[[6, 6, 7]] ≈ 1/8
end

@testset "Choice" begin
    v = @dice_ite if flip(3/5)
        DistVector([DistUInt32(1),DistUInt32(2),DistUInt32(3),DistUInt32(4)])
    else
        DistVector([DistUInt32(7),DistUInt32(6),DistUInt32(5)])
    end
    
    dist = pr(choice(v))
    @test dist[1] ≈ 3/5 * 1/4
    @test dist[2] ≈ 3/5 * 1/4
    @test dist[3] ≈ 3/5 * 1/4
    @test dist[4] ≈ 3/5 * 1/4
    @test dist[7] ≈ 2/5 * 1/3
    @test dist[6] ≈ 2/5 * 1/3
    @test dist[5] ≈ 2/5 * 1/3

    v1 = DistVector([DistUInt32(1),DistUInt32(2),DistUInt32(3),DistUInt32(4)])
    v2 = DistVector([DistUInt32(7),DistUInt32(6),DistUInt32(5)])
    ch1, evid1 = choice_obs(v1)
    ch2, evid2 = choice_obs(v2)
    ch = @dice_ite if flip(3/5)
        ch1
    else
        ch2
    end
    dist = pr(ch, evidence=evid1&evid2)
    @test dist[1] ≈ 3/5 * 1/4
    @test dist[2] ≈ 3/5 * 1/4
    @test dist[3] ≈ 3/5 * 1/4
    @test dist[4] ≈ 3/5 * 1/4
    @test dist[7] ≈ 2/5 * 1/3
    @test dist[6] ≈ 2/5 * 1/3
    @test dist[5] ≈ 2/5 * 1/3
end
