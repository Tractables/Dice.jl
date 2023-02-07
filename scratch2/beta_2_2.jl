using Dice
using Plots


f(beta, i) = 1/(1 + exp(beta/2^i))

a = uniform(DistUInt{10})
b = uniform(DistUInt{10})
c = uniform(DistUInt{10})

code = @dice begin
    observe(a < b)
    observe(b < c)
    c
end

ans1 = pr(code)
plot(ans1)
ans2 = pr(b)
plot(ans2)

ans3 = pr(d)
plot(ans3)