using Test
using Dice
using Distributions

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

@testset "num_nodes" begin
    f1 = flip(0.5)
    f2 = f1
    @test num_nodes(f1) == 3
    @test num_nodes(DistUInt{2}([f1, f2])) == 3
    @test num_nodes(uniform(DistUInt{3})) == 5
end

@testset "Cudd_RecursiveDeref GC issue" begin
    x1s = -1.359
    x2s = -0.458
    error1 = -2.25
    y1s = x1s + 2*x2s + error1
    
    X = hcat(x1s, x2s)
    S = hcat([2, 0], [0, 2])
    sigma = inv(transpose(X) * X + inv(S))
    mu = sigma * transpose(transpose(y1s) * X)
    
    bits = 7
    pieces = 2^(8)
    DFiP = DistFix{9+bits, bits}
    
    w1 = bitblast(DFiP, Normal(0, sqrt(2)), pieces, -8.0, 8.0)
    w2 = bitblast(DFiP, Normal(0, sqrt(2)), pieces, -8.0, 8.0)
    code = @dice begin
                error1 = bitblast(DFiP, Normal(0, 1), pieces, -8.0, 8.0)
                observe(prob_equals(DFiP(y1s[1]), DFiP(x1s[1])*w1 + DFiP(x2s[1])*w2 + error1))
                w1
    end
    
    @test isapprox(expectation(code), mu[1]; atol = 0.1)
end
