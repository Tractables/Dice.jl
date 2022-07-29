using Test

using Dice

@testset "Sugar Tests" begin

    # @test infer((@dice begin
    #                 f1 = flip(0.5)
    #                 a = DistSignedInt(DistInt([f1, flip(1)]))
    #                 b = DistSignedInt(DistInt([f1, flip(1), flip(0)]))
    #                 prob_equals(a, b)
    #             end), :bdd) ≈ 0.0

end