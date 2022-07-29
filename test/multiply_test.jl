using Test

# using Revise
using Dice
using Dice: CuddMgr, DistBool

@testset "Sugar Tests" begin

    @test infer((@dice prob_equals(DistSigned{5, 1}(dicecontext(), -1.0) * DistSigned{6, 2}(dicecontext(), 1.75), DistSigned{11, 3}(dicecontext(), -1.75))), :bdd) ≈ 1.0
    @test infer((@dice prob_equals(DistSigned{5, 1}(dicecontext(), 1.0) * DistSigned{6, 2}(dicecontext(), -1.75), DistSigned{11, 3}(dicecontext(), -1.75))), :bdd) ≈ 1.0
    @test infer((@dice prob_equals(DistSigned{5, 1}(dicecontext(), -1.0) * DistSigned{6, 2}(dicecontext(), -1.75), DistSigned{11, 3}(dicecontext(), 1.75))), :bdd) ≈ 1.0
    @test infer((@dice prob_equals(DistSigned{5, 1}(dicecontext(), 1.0) * DistSigned{6, 2}(dicecontext(), 1.75), DistSigned{11, 3}(dicecontext(), 1.75))), :bdd) ≈ 1.0

    @test infer((@dice begin
                    a = uniform(dicecontext(), 2, DistSigned{5, 1})
                    b = uniform(dicecontext(), 3, DistSigned{6, 2})
                    prob_equals(a * b, DistSigned{11, 3}(dicecontext(), 0.0))
    end), :bdd) ≈ 0.34375

end