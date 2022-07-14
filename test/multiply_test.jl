using Test

# using Revise
using Dice
using Dice: CuddMgr, DistBool

@testset "Sugar Tests" begin

    @test infer((@dice prob_equals(DistSigned{3, 1}(dicecontext(), -1.0) * DistSigned{4, 2}(dicecontext(), 1.75), DistSigned{7, 3}(dicecontext(), -1.75))), :bdd) ≈ 1.0

end