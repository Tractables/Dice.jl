using Dice
using Plots

f(beta, i) = 1/(1 + exp(beta/2^i))

# Get (e^(x^2) - 1) density
a = convert(uniform(DistUInt{7}), DistUInt{14})
b = DistUInt{14}([flip(f(100, i)) for i in 1:14])

function mux(a, x, k)
    value = true
    for i=1:2^k
        if prob_equals(a, DistUInt{k}(i-1))
            value = value & (x.bits[i])
        end
    end
    return value
end

a = DistUInt{3}(2)
x = DistUInt{8}([true, false, true, false, true, false, true, false])
mux(a, x, 3)


bitwidth = 4
a = DistUInt{bitwidth}([flip(f(100, i)) for i in 1:bitwidth])
x = DistUInt{2^(bitwidth)}([flip(f(0, i)) for i in 1:2^(bitwidth)])

a = uniform(DistUInt{bitwidth})
x = uniform(DistUInt{2^bitwidth})
code = @dice begin
     observe(!mux(a, x, bitwidth))
     a
end

ans1 = Dict((b, log(a)) for (b, a) in pr(code))
plot(ans1)
# ans2 = map(a-> (a[1], log(a[2])), pr(x))

ans2 = Dict((b, log(a)) for (b, a) in pr(a))
plot!(ans2)