using Pkg; Pkg.activate(@__DIR__);

using Test

using Dice
using Dice: CuddMgr, DistBool

@testset "DistBool Tests" begin
    
    mgr = CuddMgr()

    t = DistBool(mgr, true)
    f = DistBool(mgr, false)
    x = DistBool(mgr, 0.5)

    @test Dice.isvalid(prob_equals(x & t, x))
    @test Dice.isvalid(prob_equals(x & f, f))
    @test Dice.isvalid(prob_equals(x | t, t))
    @test Dice.isvalid(prob_equals(x | f, x))


    @test Dice.isvalid(prob_equals(x & true, x))
    @test Dice.isvalid(prob_equals(true & x, x))
    @test Dice.isvalid(prob_equals(x & false, f))
    @test Dice.isvalid(prob_equals(false & x, f))
    @test Dice.isvalid(prob_equals(x | true, t))
    @test Dice.isvalid(prob_equals(true | x, t))
    @test Dice.isvalid(prob_equals(x | false, x))
    @test Dice.isvalid(prob_equals(false | x, x))

    @test Dice.isvalid(prob_equals(x & x, x))
    @test Dice.isvalid(prob_equals(x | x, x))

end
