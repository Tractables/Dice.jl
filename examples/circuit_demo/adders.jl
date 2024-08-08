using Dice
using DelimitedFiles

#= 
    Contains functions implementing a half adder, (one bit) full adder, and
    arbitrary addition. Also gives an example call for each function with probabilistic input.
=#

# Half adder function
function half_adder(a, b)
    summ = xor(a, b)
    carry = a & b
    return summ, carry
end

# Distribution of half adder outputs when both inputs are 1 with probability 0.5
pr(half_adder(flip(0.5), flip(0.5)))


# One-bit full adder based on half adder 
function full_adder(a, b, c)
    s1, c1 = half_adder(a, b)
    s2, c2 = half_adder(s1, c)
    c3 = c1 | c2
    return s2, c3
end

# Distribution of full adder outputs when each input is 1 with probability 0.5
pr(full_adder(flip(0.5), flip(0.5), flip(0.5)))


# Arbitrary bit adder made by chaining full adders
# This is in essence how the probabilistic (+) is implemented 
function add(a::DistUInt{W}, b::DistUInt{W}) where W
    # a DistUInt{W} is a probabilistic integer over W bits
    summ = Vector(undef, W)
    carry = false
    for i in W:-1:1
        # print(i)
        summ[i], carry = full_adder(a.bits[i], b.bits[i], carry)
    end
    return DistUInt{W}(summ)
end

# Addition on uniform distributions over 3-bit (unsigned) integers
a = uniform(DistUInt{3})
b = uniform(DistUInt{3})
pr(add(a, b))