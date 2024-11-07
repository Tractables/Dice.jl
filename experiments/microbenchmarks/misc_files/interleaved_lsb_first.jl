using Dice

localARGS = ARGS
num_bits = parse(Int64, localARGS[1])

i = num_bits

a_b = Vector(undef, i+1)
b_b = Vector(undef, i+1)
a_b[1] = false
b_b[1] = false
for j=(i+1):-1:2
    a_b[j]=flip(0.5)
    b_b[j]=flip(0.5)
end
    
a = DistUInt(a_b)
b = DistUInt(b_b)

#~begin less
println(pr(a < b))
#~end

#~begin equals
println(pr(prob_equals(a, b)))
#~end

#~begin sum
println(expectation(a + b))
#~end