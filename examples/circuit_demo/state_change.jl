using Dice
using DelimitedFiles
using Plots

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
    carry = Vector(undef, W)
	carry_temp = false
    for i in W:-1:1
        # print(i)
        summ[i], carry_temp = full_adder(a.bits[i], b.bits[i], carry_temp)
		carry[i] = carry_temp
    end
    return DistUInt{W}(summ), carry
end

a = uniform(DistUInt{3})
b = uniform(DistUInt{3})
s1, c1 = add(a, b)

a = uniform(DistUInt{3}, 2)
b = uniform(DistUInt{3}, 2)
s2, c2 = add(a, b)

carry_changes = DistUInt{3}(0)
for i in 1:3
	carry_changes += ifelse(!prob_equals(c1[i], c2[i]), DistUInt{3}(1), DistUInt{3}(0))
end
result = pr(carry_changes)
bar(ans, xlabel="Number of carry changes", ylabel="pr", legend=false)
# pr(!prob_equals(c1[1], c2[1]) | !prob_equals(c1[2], c2[2]) | !prob_equals(c1[3], c2[3]))