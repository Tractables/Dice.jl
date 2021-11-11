using Test

using Dice
using Dice: CuddMgr, DistBool

@testset "Cudd Backend Tests" begin
    
    mgr = CuddMgr()

    x = DistBool(mgr, 0.5)

    @test !!x == x
    @test isliteral(x)
    @test isliteral(!x)

end
