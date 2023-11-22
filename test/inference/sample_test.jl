using Test
using Dice

@testset "Sample tests" begin
    # This test flakes with probability O(1/2^RUNS)
    RUNS = 200

    x = DistUInt{3}([flip(.5), true, true])
    samples = [sample(x) for _ in 1:RUNS]
    @test Set(samples) == Set([3, 7])

    x = DistUInt{3}([flip(.5), true, flip(.99)])
    is_even(n::T) where T = prob_equals(T(0), n % T(2))
    samples = [sample(x, evidence=is_even(x)) for _ in 1:RUNS]    
    @test Set(samples) == Set([2, 6])
end
