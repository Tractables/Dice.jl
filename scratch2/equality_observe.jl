using Dice
using Plots


f(beta, i) = 1/(1 + exp(beta/2^i))

a = uniform(DistUInt{10})
b = DistUInt{10}([flip(f(10, i)) for i in 1:10])
c = DistUInt{10}([flip(f(-5, i)) for i in 1:10])
d = DistUInt{10}([flip(f(5, i)) for i in 1:10])
code = @dice begin
    observe(prob_equals(b, c))
    b
end

ans1 = pr(code)
plot(ans1)
ans2 = pr(b)
plot(ans2)

ans3 = pr(d)
plot(ans3)