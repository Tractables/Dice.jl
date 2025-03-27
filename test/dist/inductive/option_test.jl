using Test
using Alea

@testset "Option test" begin
    none_int = Opt.None(DistUInt32)
    none_string = Opt.None(DistString)
    @test_throws MethodError prob_equals(none_int, none_string)

    dist = pr(prob_equals(none_int, Opt.None(DistUInt32)))
    @test dist[true] == 1

    probably_none = @alea_ite if flip(9/10)
        Opt.None(DistString)
    else
        Opt.Some(
            DistString,
            @alea_ite if flip(2/3)
                DistString("foo")
            else
                DistString("")
            end
        )
    end
    res = match(probably_none, [
        :Some => (s) -> s + DistString("bar"),
        :None => () -> DistString("impossible")
    ])
    evid = !prob_equals(res, DistString("impossible"))
    @test pr(res, evidence=evid)["foobar"] ≈ 2/3
    @test pr(matches(probably_none, :None))[true] ≈ 9/10
    @test pr(matches(probably_none, :Some))[true] ≈ 1/10
end


@testset "Right thunks called" begin
    none_str = Opt.None(DistString)
    some_str = Opt.Some(DistString, DistString("hi"))

    error_none1(x) = match(x, [
        :None => ()  -> error()
        :Some => (_) -> DistUInt(5)
    ])
    error_none2(x) = match(x, [
        :Some => (_) -> DistUInt(5)
        :None => ()  -> error()
    ])

    error_some1(x) = match(x, [
        :Some => (_) -> error()
        :None => ()  -> DistUInt(5)
    ])
    error_some2(x) = match(x, [
        :None => ()  -> DistUInt(5)
        :Some => (_) -> error()
    ])
    
    @test_throws ErrorException error_none1(none_str)
    @test_throws ErrorException error_none2(none_str)

    @test_throws ErrorException error_some1(some_str)
    @test_throws ErrorException error_some2(some_str)

    @test pr(error_none1(some_str)) == Dict(5 => 1.)
    @test pr(error_none2(some_str)) == Dict(5 => 1.)

    @test pr(error_some1(none_str)) == Dict(5 => 1.)
    @test pr(error_some2(none_str)) == Dict(5 => 1.)
end
