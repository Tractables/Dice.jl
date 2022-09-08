using Test
using Dice
using Dice: canonicalize, optimize_unsat, optimize_condition, num_ir_nodes

@testset "canonicalize" begin
    
    f1, f2, f3, f4, f5 = [flip(0.5) for _ = 1:5]

    x = (f1 & f2) | !(f3 & (f2 & f1))

    @test num_ir_nodes(x) == 8
    xc, _ = canonicalize(x)
    @test num_ir_nodes(xc) == 7
end


@testset "optimize_unsat" begin
    
    f1, f2, f3, f4, f5 = [flip(0.5) for _ = 1:5]

    x = !f5 & (f5 | (f4 & !((f1 | f2) | (!f2 | f3))))
    @test Dice.optimize_unsat(x) == false

    x = (f1 | f2) & f1
    @test Dice.optimize_unsat(x) == f1
end



@testset "optimize_condition" begin
    
    f1, f2, f3, f4, f5 = [flip(0.5) for _ = 1:5]
    
    x = (f1 & f2) & (f1 | f3) 

    @test Dice.num_ir_nodes(x) == 6

    x = Dice.optimize_condition(x);

    @test Dice.num_ir_nodes(x) == 3

    # this should work eventually
    # x = (f1 & f2) | (f1 & !f2)
    # @test Dice.optimize_***(x) == f1


end