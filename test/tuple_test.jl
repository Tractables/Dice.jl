using Test
using Alea
using Alea: Flip, num_ir_nodes
using Distributions

@testset "Probabilistic Tuples" begin
    
    x = @dice begin
        (flip(0.2), false, uniform(DistUInt{3}))
    end;

    @test pr(x)[(false, false, 3)] ≈ 0.8/2^3

    cg = @dice begin
        x = (flip(0.2), false, uniform(DistUInt{3}))
        if flip(0.5)
            (false, false, DistUInt{3}(3))
        else
            x
        end
    end
    @test pr(cg)[(false, false, 3)] ≈ 0.5 + 0.5 * 0.8/2^3
end
