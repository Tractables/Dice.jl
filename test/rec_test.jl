using Test

using Dice
using Dice: DistBool

code = @dice_ite begin
    function test_rec(a::Int)
        if a <= 0
            flip(0.5)
        else
            flip(0.5) & test_rec(a - 1)
        end
    end

    test_rec(2)
end

@testset "Sugar Tests" begin
    
    @test infer_bool((@dice_ite if flip(0.5) flip(0.1) else flip(0.3) end)) ≈ 0.2
    @test infer_bool((@dice_ite if true flip(0.1) else flip(0.2) end)) ≈ 0.1

    @test infer_bool(code) ≈ 0.125

end