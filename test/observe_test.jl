using Test

using Dice
using Dice: DistBool

@testset "Sugar Tests" begin
    
    @test infer((@dice_ite CondBool(flip(0.5), flip(0.5)))) ≈ 0.5
    @test infer((@dice_ite begin 
                       a = flip(0.5)
                       CondBool(a, a)
                       end)) ≈ 1

    @test infer((@dice_ite begin 
                        a = flip(0.5)
                        CondBool(a, !a)
                        end)) ≈ 0

end