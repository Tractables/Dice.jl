using Dice
using DelimitedFiles

function half_adder(a, b)
    summ = xor(a, b)
    carry = a & b
    return summ, carry
end

pr(half_adder(flip(0.5), flip(0.5)))

function full_adder(a, b, c)
    s1, c1 = half_adder(a, b)
    s2, c2 = half_adder(s1, c)
    c3 = c1 | c2
    return s2, c3
end

pr(full_adder(flip(0.5), flip(0.5), flip(0.5)))


function add(a::DistUInt{W}, b::DistUInt{W}) where W
    summ = Vector(undef, W)
    carry = false
    for i in W:-1:1
        # print(i)
        summ[i], carry = full_adder(a.bits[i], b.bits[i], carry)
    end
    return DistUInt{W}(summ)
end

a = uniform(DistUInt{3})
b = uniform(DistUInt{3})
pr(add(a, b))