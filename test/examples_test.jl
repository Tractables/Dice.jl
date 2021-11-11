using Test
using Suppressor: @suppress_out

@testset "Example Directory Tests" begin
    
    @test_nowarn @suppress_out include(
        "$(@__DIR__)/../examples/mapreduce.jl")

end
