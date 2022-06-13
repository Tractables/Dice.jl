using Test

using Dice
using Dice: CuddMgr, DistBool

@testset "Sugar Tests" begin
    
    @test infer_bool(@dice flip(0.5)) ≈ 0.5
    @test infer_bool((@dice DistBool(0.5))) ≈ 0.5

    @test infer_bool((@dice prob_equals(DistInt(42), 42))) ≈ 1

end
