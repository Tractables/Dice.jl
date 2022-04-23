using Test
using Suppressor: @suppress_out

@testset "Example Directory Tests" begin
    
    @test_nowarn @suppress_out include(
        "$(@__DIR__)/../examples/mapreduce.jl")

    @test_nowarn @suppress_out include(
        "$(@__DIR__)/../examples/test_divide.jl"
    )

    @test_nowarn @suppress_out include(
        "$(@__DIR__)/../examples/test_mod.jl"
    )

    @test_nowarn @suppress_out include(
        "$(@__DIR__)/../examples/test_discrete.jl"
    )

    @test_nowarn @suppress_out include(
        "$(@__DIR__)/../examples/test_arith.jl"
    )

    @test_nowarn @suppress_out include(
        "$(@__DIR__)/../examples/test_condint.jl"
    )

    @test_nowarn @suppress_out include(
        "$(@__DIR__)/../examples/test_infer.jl"
    )

    @test_nowarn @suppress_out include(
        "$(@__DIR__)/../examples/test_char.jl"
    )

    @test_nowarn @suppress_out include(
        "$(@__DIR__)/../examples/test_ifelse.jl"
    )

end
