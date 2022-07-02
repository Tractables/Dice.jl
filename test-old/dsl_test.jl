using Test

using Dice
using Dice: CuddMgr, DistBool

@testset "Sugar Tests" begin
    

    @test infer_bool((@dice_ite prob_equals(DistInt(42), 42))) ≈ 1

end
