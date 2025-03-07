using Test
using Dice
using Dice: Flip, num_ir_nodes

@testset "VarOrder Interleaving - Addition" begin

    d = uniform(DistUInt{3}, 2)
    e = uniform(DistUInt{3}, 2)
    f = d+e
    @test num_nodes(f) == 13

    a = uniform(DistUInt{4}, 3)
    b = uniform(DistUInt{4}, 3)
    c = a+b
    @test num_nodes(c) == 22

    g = uniform(DistUInt{8}, 7)
    h = uniform(DistUInt{8}, 7)
    i = g+h
    @test num_nodes(i) == 58

    # hi

end