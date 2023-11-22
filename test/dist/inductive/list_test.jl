using Test
using Dice

dist_type(::Integer) = DistUInt32
dist_type(::String) = DistString

function to_dist_list(v)
    t = if isempty(v) DistUInt32 else dist_type(first(v)) end
    res = DistNil(t)
    for x in Iterators.reverse(v)
        res = DistCons(t(x), res)
    end
    res
end

function to_ast(v)
    Dice.frombits(to_dist_list(v), Dict())
end

@testset "DistList core" begin
    # Test concatenation, appending, ifelse
    v = @dice_ite if flip(3/5)
        to_dist_list([1, 2, 3, 4])
    else
        to_dist_list([7, 6, 5])
    end
    v = @dice_ite if flip(2/3) prob_append(v, DistUInt32(100)) else v end
    v2 = @dice_ite if flip(1/10)
        to_dist_list([333, 444])
    else
        to_dist_list([555])
    end
    cg = concat(v, v2)
    dist = pr(cg)
    @test sum(values(dist)) ≈ 1
    @test dist[to_ast([1, 2, 3, 4, 100, 333, 444])] ≈ 3/5 * 2/3 * 1/10
    @test dist[to_ast([1, 2, 3, 4, 100, 555])] ≈ 3/5 * 2/3 * 9/10
    @test dist[to_ast([1, 2, 3, 4, 333, 444])] ≈ 3/5 * 1/3 * 1/10
    @test dist[to_ast([1, 2, 3, 4, 555])] ≈ 3/5 * 1/3 * 9/10
    @test dist[to_ast([7, 6, 5, 100, 333, 444])] ≈ 2/5 * 2/3 * 1/10
    @test dist[to_ast([7, 6, 5, 100, 555])] ≈ 2/5 * 2/3 * 9/10
    @test dist[to_ast([7, 6, 5, 333, 444])] ≈ 2/5 * 1/3 * 1/10
    @test dist[to_ast([7, 6, 5, 555])] ≈ 2/5 * 1/3 * 9/10

    cg = @dice begin
        v1 = DistNil(DistUInt32)
        v2 = ifelse(flip(1/2), prob_append(v1, DistUInt32(6)), v1)
        v3 = ifelse(flip(1/2), prob_append(v2, DistUInt32(7)), v2)
        ifelse(flip(1/2), prob_append(v3, DistUInt32(6)), v3)
    end
    dist = pr(cg)
    @test length(dist) == 7
    @test dist[to_ast([])] ≈ 1/8
    @test dist[to_ast([7])] ≈ 1/8
    @test dist[to_ast([6])] ≈ 1/4
    @test dist[to_ast([6, 6])] ≈ 1/8
    @test dist[to_ast([6, 7])] ≈ 1/8
    @test dist[to_ast([7, 6])] ≈ 1/8
    @test dist[to_ast([6, 7, 6])] ≈ 1/8
    
    # Test prob_equals
    x = prob_equals(
        to_dist_list([1,2]),
        ifelse(flip(0.5),
            to_dist_list([1,2,3]),
            ifelse(flip(0.1),
                to_dist_list([1,2]),
                DistNil(DistUInt32))))
    @test pr(x)[true] ≈ 0.5 * 0.1

    # Test concatenation for empty vectors
    cg = @dice begin
        concat(DistNil(DistUInt32), DistNil(DistUInt32))
    end
    dist = pr(cg)
    @test sum(values(dist)) ≈ 1
    @test dist[to_ast([])] ≈ 1
    
    
    cg = @dice begin
        concat(DistNil(DistString), DistCons(DistString("hi"), DistNil(DistString)))
    end
    dist = pr(cg)
    @test sum(values(dist)) ≈ 1
    @test dist[to_ast(["hi"])] ≈ 1

    foo_bar = to_dist_list(["foo", "bar"])
    cg = one_of(ifelse(flip(2/3), DistNil(DistString), foo_bar))
    dist = pr(cg)
    @test sum(values(dist)) == 1
    @test dist[("None", [])] ≈ 2/3
    @test dist[("Some", ["foo"])] ≈ 1/6
    @test dist[("Some", ["bar"])] ≈ 1/6
end
