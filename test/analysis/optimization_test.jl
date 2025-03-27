using Test
using Alea
using Alea: canonicalize, optimize_unsat, optimize_condition, num_ir_nodes

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
    @test Alea.optimize_unsat(x) == false

    x = (f1 | f2) & f1
    @test Alea.optimize_unsat(x) == f1
end



@testset "optimize_condition" begin
    
    f1, f2, f3, f4, f5 = [flip(0.5) for _ = 1:5]
    
    x = (f1 & f2) & (f1 | f3) 

    @test Alea.num_ir_nodes(x) == 6

    x = Alea.optimize_condition(x);

    @test Alea.num_ir_nodes(x) == 3

    # this should work eventually
    # x = (f1 & f2) | (f1 & !f2)
    # @test Alea.optimize_***(x) == f1


end

@testset "optimize_condition_global" begin
    
    n = 3
    grid = Matrix{Dist{Bool}}(undef, n, n);
    for i=1:n, j=1:n
        pa1 = i==1 ? false : grid[i-1,j  ]
        pa2 = j==1 ? false : grid[i,  j-1]
        grid[i,j] = ifelse(pa1, 
                        ifelse(pa2, flip(0.1), flip(0.2)), 
                        ifelse(pa2, flip(0.3), flip(0.4)))
    end
    evidence = reduce(&, grid)
    evidence_opt = Alea.optimize_condition_global(evidence)

    @test pr(evidence)[true] ≈ pr(evidence_opt)[true]
    @test num_ir_nodes(evidence) > num_ir_nodes(evidence_opt)

end
