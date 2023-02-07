using Dice
using Plots

f(beta, i) = 1/(1 + exp(beta/2^i))

# Get (e^(x^2) - 1) density
a = convert(uniform(DistUInt{7}), DistUInt{14})
b = DistUInt{14}([flip(f(100, i)) for i in 1:14])

code = @dice begin
            observe(b < a*a)
            observe(a < DistUInt{14}(25))
            a
end

ans1 = pr(code)
plot(ans1)

# Get (e^(x^2)) density 
a = convert(uniform(DistUInt{7}), DistUInt{14})
b = DistUInt{14}([flip(f(-4, i)) for i in 1:14])
d = uniform(DistUInt{14})

code = @dice begin
            observe(b < a*a)
            
            shifted = if flip(1/exp(-4)) d else a end
            shifted
end

ans2 = pr(code)
ans3 = filter(a -> a[1] < 128, ans2)
plot(ans3)