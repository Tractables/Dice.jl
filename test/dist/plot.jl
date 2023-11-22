#==
using Test
using Dice
using TikzGraphs
using TikzPictures

@testset "Plot" begin
    
    f1, f2 = flip(0.1), flip(0.6) 
    x = f1 & !f2 | !f1 & f2
    
    tp = TikzGraphs.plot(x)
    @test tp isa TikzPicture

    mktempdir() do path
        @test_nowarn save(PDF("$path/test.pdf"), tp)
        @test_nowarn save(SVG("$path/test.svg"), tp)
    end

end
==#