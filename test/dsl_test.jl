using Test

using Dice
using Dice: CuddMgr, DistBool

@testset "Sugar Tests" begin
    
    @test infer((@dice flip(0.5)), :bdd) ≈ 0.5
    @test infer((@dice DistBool(dicecontext(), 0.5)), :bdd) ≈ 0.5

    @test infer((@dice prob_equals(ProbInt(42), 42)), :bdd) ≈ 1
    @test infer((@dice prob_equals(ProbInt(dicecontext(), 42), 42)), :bdd) ≈ 1

end
