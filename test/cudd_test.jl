using Test

using Dice
using Dice: CuddMgr, DistBool

@testset "Cudd Backend Tests" begin
    
    mgr = CuddMgr()

    x = DistBool(mgr, 0.5)

    @test !!x == x
    @test Dice.isliteral(x)
    @test Dice.isliteral(!x)

    @test Dice.isposliteral(x)
    @test Dice.isnegliteral(!x)

    @test !Dice.isposliteral(!x)
    @test !Dice.isnegliteral(x)

end
