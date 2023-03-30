using Revise
using Dice
using Test
using TikzGraphs
using TikzPictures

n = 4
v = Vector(undef, n)
for i in 1:n
    v[i] = ifelse(flip(0.5), DistUInt{5}(0), DistUInt{5}(1))
end

a1 = v[1] + v[2]
a2 = v[3]+ v[4]
a3 = v[5] + v[6]
a4 = v[7] + v[8]

b1 = a1 + a2
b2 = a3 + a4

sum = b1

y = (sum > DistUInt{5}(Int(ceil(n/2))))

y = atleast_two(v[1], v[2], v[3])

save(PDF("./test.png"), y)
