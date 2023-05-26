using Dice

localARGS = ARGS
num_bits = parse(Int64, localARGS[1])
nbpow = 2^num_bits

a = discrete(DistUInt{num_bits+1}, [1/nbpow for _ in 1:nbpow])
b = discrete(DistUInt{num_bits+1}, [1/nbpow for _ in 1:nbpow])

#~begin less
println(pr(a < b))
#~end

#~begin equals
println(pr(prob_equals(a, b)))
#~end

#~begin sum
println(expectation(a + b))
#~end