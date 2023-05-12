using Test
using Dice

@testset "Option test" begin
    none_int = DistNone(DistUInt32)
    none_string = DistNone(DistString)
    @test_throws MethodError prob_equals(none_int, none_string)

    dist = pr(prob_equals(none_int, DistNone(DistUInt32)))
    @assert dist[true] == 1

    probably_none = @dice_ite if flip(9/10)
        DistNone(DistString)
    else
        DistSome(
            @dice_ite if flip(2/3)
                DistString("foo")
            else
                DistString("")
            end
        )
    end
    res = match(probably_none, [
        "Some" => (s) -> s + DistString("bar"),
        "None" => ()  -> DistString("impossible")
    ])
    evid = !prob_equals(res, DistString("impossible"))
    @test pr(res, evidence=evid)["foobar"] ≈ 2/3
end
