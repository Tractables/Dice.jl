using Test

using Dice
using Dice: CuddMgr, DistBool

@testset "Sugar Tests" begin
    
    @test infer((@dice begin
                        a = DistFixParam{2, 1}([flip(0.5), flip(0.5)])
                        b = DistFixParam{2, 1}([flip(0.5), flip(0.5)])
                        prob_equals((a/b)[1], 1) 
                       end), :bdd) ≈ 0.25
    @test infer((@dice DistBool(dicecontext(), 0.5)), :bdd) ≈ 0.5

    @test infer((@dice prob_equals(DistInt(42), 42)), :bdd) ≈ 1
    @test infer((@dice prob_equals(42, DistInt(42))), :bdd) ≈ 1
    @test infer((@dice prob_equals(DistInt(dicecontext(), 42), 42)), :bdd) ≈ 1

end