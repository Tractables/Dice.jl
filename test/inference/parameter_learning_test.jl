using Revise
using Dice
using Test
using TikzGraphs
using TikzPictures

n = 5
v = Vector(undef, n)
for i in 1:n
    v[i] = ifelse(flip(0.5), DistUInt{5}(0), DistUInt{5}(1))
end

sum = DistUInt{5}(0)
for i in 1:n
    sum = sum + v[i]
end
y = (sum > DistUInt{5}(Int(ceil(n/2))))

tp = TikzGraphs.plot(y)
@test tp isa TikzPicture
save(PDF("test.pdf"), tp)
        @test_nowarn save(SVG("$path/test.svg"), tp)
    end


save("yo.png", y)