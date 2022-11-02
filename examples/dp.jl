using Revise
using Dice, Distributions

t = @dice begin
    a1 = flip(0.5)
    a2 = flip(0.5)
    a3 = flip(0.5)
    a4 = flip(0.5)
    a5 = flip(0.5)

    sum = DistInt{5}(0)
    sum = ifelse(a1, sum+DistInt{5}(1), sum)
    sum = ifelse(a2, sum+DistInt{5}(1), sum)
    sum = ifelse(a3, sum+DistInt{5}(1), sum)
    sum = ifelse(a4, sum+DistInt{5}(1), sum)
    sum = ifelse(a5, sum+DistInt{5}(1), sum)

    observe(sum + uniform(DistInt{5}, -2, 2) == DistInt{5}(3))
    # DistUInt{5}([a1, a2, a3, a4, a5])
    sum
end

pr(t)