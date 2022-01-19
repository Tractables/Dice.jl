using Revise
using Test
using Suppressor: @suppress_out

@testset "Example Directory Tests" begin
    
    @test_nowarn @suppress_out include(
        "$(@__DIR__)/../examples/mapreduce.jl")

    @test_nowarn include(
        "$(@__DIR__)/../examples/test_divide.jl"
    )

    @test_nowarn include(
        "$(@__DIR__)/../examples/test_mod.jl"
    )

    

end
