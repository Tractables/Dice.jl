using Dice

localARGS = ARGS
num_bits = parse(Int64, localARGS[1])

a = uniform(DistUInt{num_bits+1}, 0, 2^num_bits)
b = uniform(DistUInt{num_bits+1}, 0, 2^num_bits)

#~begin less
println(pr(a < b))
#~end

#~begin equals
println(pr(prob_equals(a, b)))
#~end

#~begin sum
println(expectation(a + b))
#~end