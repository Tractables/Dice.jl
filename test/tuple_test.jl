using Test
using Dice
using Dice: Flip, num_ir_nodes
using Distributions

@testset "Probabilistic Tuples" begin
    
    x = @dice begin
        (flip(0.2), false, uniform(DistUInt{3}))
    end;

    @test pr(x)[(false, false, 3)] ≈ 0.8/2^3

end
