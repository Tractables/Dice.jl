using Test

using Dice
using Dice: DistBool


# @testset "Cudd Backend Tests" begin
    
#     mgr = CuddMgr()

#     x = DistBool(mgr, 0.1)

#     @test !!x == x
#     @test Dice.isliteral(x)
#     @test Dice.isliteral(!x)

#     @test Dice.isposliteral(x)
#     @test Dice.isnegliteral(!x)

#     @test !Dice.isposliteral(!x)
#     @test !Dice.isnegliteral(x)

#     @test !Dice.Cudd_IsComplement(x.bit)
#     @test Dice.Cudd_IsComplement((!x).bit)

#     @test Dice.Cudd_Regular(x.bit) === x.bit
#     @test Dice.Cudd_Regular((!x).bit) === x.bit

#     # @test infer(x) ≈ 0.1
#     # @test infer(!x) ≈ 0.9

# end
