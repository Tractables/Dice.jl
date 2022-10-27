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

@testset "Probabilistic Matrix" begin
    
    x = [DistUInt{3}([false,false,flip(1.0/(i+j))]) for i=1:2, j=1:2]
    @test getindex.(pr.(x), 1) ≈ [0.5 0.3333333333333333; 0.3333333333333333 0.25]

    # TODO next test is too slow, speed up dynamo
    # y = @dice begin
    #     x*x
    # end

    # pr(y)[[0 0; 0 0]] ≈ 0.333333

end

