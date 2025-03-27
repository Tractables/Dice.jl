using Alea
using Plots

f1 = flip(0.1)
f2 = flip(0.2)
f3 = flip(0.3)

n = 10
beta = 3
f = [flip(exp(beta/2^i)/(1 + exp(beta/2^i))) for i in 1:n]

change = ifelse(f[1], f[2], f[3])
bits = vcat([f[1], change], f[3:n])



b1 = f1
b2 = ifelse(f1, f2, f3)
b3 = f3

p = DistUInt{n}(bits)



scatter(pr(p))

scatter!(pr(DistUInt{n}(f)))

a = pr(p)
sum([i[2] for i in a])

b = pr(DistUInt{n}(f))
sum([i[2] for i in b])