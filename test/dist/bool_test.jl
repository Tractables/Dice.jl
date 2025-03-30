using Test
using Alea
using Alea: Flip, num_ir_nodes

@testset "DistBool core" begin
    
    @test flip(0.5).prob ≈ 0.5
    @test flip(0.9).prob ≈ 0.9 

    @test true & flip(0.5) isa Flip
    @test false & flip(0.5) == false
    
    @test flip(0.5) & true isa Flip
    @test flip(0.5) & false == false

    @test true | flip(0.5)  == true
    @test false | flip(0.5) isa Flip
    
    @test flip(0.5) | true == true
    @test flip(0.5) | false isa Flip
    
    @test num_ir_nodes(flip(0.5) & flip(0.5)) == 3
    @test num_ir_nodes(flip(0.5) | flip(0.5)) == 3

    f = flip(0.5)
    @test !f != f
    @test num_ir_nodes(!f) == 2
    @test !!f == f

    @test flip(0.0) == false
    @test flip(1.0) == true

    @test flip(1.0) & flip(0.5) isa Flip

    @test flip(0.5).global_id > f.global_id

    @test num_ir_nodes(flip(0.5) < flip(0.5)) == 4

    @test prob_equals(true,true)
    @test prob_equals(false,false)
    @test !prob_equals(true,false)
    @test prob_equals(true, f) == f
    @test prob_equals(false, !f) == f
    @test prob_equals(f, f) 
    @test pr(prob_equals(flip(0.5),flip(0.5)))[true] ≈ 0.5
    @test num_ir_nodes(prob_equals(flip(0.5),flip(0.5))) == 6

    @test !xor(true,true)
    @test !xor(false,false)
    @test xor(true,false)
    @test !xor(true, f) == f
    @test !xor(false, !f) == f
    @test !xor(f, f) 
    @test xor(f,f,f) == f
    @test xor(!f,f)
    @test xor(f,false,f,true)

    g = flip(0.5)
    @test ifelse(true, f, g) == f
    @test ifelse(false, f, g) == g
    @test num_ir_nodes(ifelse(f, f, g)) == 3
    @test num_ir_nodes(ifelse(g, f, g)) == 3
    @test num_ir_nodes(ifelse(flip(0.5), f, g)) == 7
    @test ifelse(flip(0.5), f, f) == f
    
end

@testset "DistBool probability" begin
    @test pr(flip(0.78))[true] ≈ 0.78
    @test pr(flip(0.78) & flip(0.41))[true] ≈ 0.78 * 0.41
    @test pr(flip(0.78) | flip(0.41))[true] ≈ 1 - (1-0.78) * (1-0.41)

    f = flip(0.78)
    @test pr(f & f)[true] ≈ 0.78
    @test pr(f | f)[true] ≈ 0.78
    @test pr(f | !f)[true] ≈ 1.00
    @test pr(f & !f)[true] ≈ 0.00

    @test pr(false)[true] ≈ 0.00
    @test pr(true)[true] ≈ 1.00

    @test expectation(f) ≈ 0.78
    @test variance(f) ≈ 0.78*(1-0.78)
end

@testset "DistBool mapreduce" begin

    probs = [1/i for i=2:20]
    x = mapreduce(p -> !flip(p), &, probs)  # all tails

    @test num_ir_nodes(x) == 19+18+1
    @test pr(x)[true] ≈ prod(1 .- probs)

end