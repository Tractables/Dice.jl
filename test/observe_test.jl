using Test

using Dice
using Dice: CuddMgr, DistBool

@testset "Sugar Tests" begin
    
    @test infer((@dice flip(0.5), flip(0.5)), :bdd) ≈ 0.5
    @test infer((@dice begin 
                       a = flip(0.5)
                       a, a
                       end), :bdd) ≈ 1

    @test infer((@dice begin 
                        a = flip(0.5)
                        a, !a
                        end), :bdd) ≈ 0

end