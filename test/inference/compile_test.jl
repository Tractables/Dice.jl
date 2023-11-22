using Test
using Dice

@testset "BDDCompiler" begin
    f1 = flip(0.5)
    f2 = flip(0.5)
    x = ((f1 & f2) | (f1 & !f2)) & !f1
    c = BDDCompiler()
    @test !Dice.issat(c.mgr, compile(c, x))
    @test Dice.isvalid(c.mgr, compile(c, !x))

    @test Dice.issat(c.mgr, compile(c, f1))
    @test !Dice.isvalid(c.mgr, compile(c, f1))
end
