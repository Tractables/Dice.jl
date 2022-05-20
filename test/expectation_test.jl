using Test

using Dice
using Dice: CuddMgr, DistBool

@testset "Sugar Tests" begin
    
    @test expectation((@dice (flip(0.2))), :bdd) ≈ 0.2
    @test expectation((@dice begin 
                       a = uniform(dicecontext(), 2, DistInt)
                       a
                       end), :bdd) ≈ 1.5
    @test expectation((@dice begin 
                    a = uniform(dicecontext(), 2, DistFixParam{3, 2})
                    a
                    end), :bdd) ≈ 1.5/4

    # @test infer((@dice begin 
    #                     a = flip(0.5)
    #                     Cond(a, !a)
    #                     end), :bdd) ≈ 0

end