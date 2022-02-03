using Test

using Dice
using Dice: CuddMgr, DistBool

code = @dice begin
    function test_rec(a::Int)
        ans = if a <= 0
                    flip(0.5)
        else
            flip(0.5) & test_rec(a - 1)
        end
    end

    test_rec(2)
end

@testset "Sugar Tests" begin
    
    @test infer((@dice if flip(0.5) flip(0.1) else flip(0.3) end), :bdd) ≈ 0.2
    @test infer((@dice if true flip(0.1) else flip(0.2) end), :bdd) ≈ 0.1

    @test infer(code, :bdd) ≈ 0.125

end