using Test
using Dice

@testset "optimize_unsat" begin
    
    f1, f2, f3, f4, f5 = [flip(0.5) for _ = 1:5]
    x = !f5 & (f5 | (f4 & !((f1 | f2) | (!f2 | f3))))

    y, canonical = Dice.canonicalize(x);
    @test Dice.num_ir_nodes(y) == 14

    universe = Dice.reused_nodes(y);
    @test length(universe) == 2

    _, conditions = Dice.unitconditions(y, universe);
    z = Dice.optimize_unsat(y, universe, conditions, canonical);
    @test z == false

end
