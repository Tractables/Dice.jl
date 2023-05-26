using Dice

localARGS = ARGS
num_bits = parse(Int64, localARGS[1])
nbpow = 2^num_bits

function discrete_sbk(probs, i=0)
    prefix_sum = [0.]
    for prob in probs
        push!(prefix_sum, last(prefix_sum) + prob)
    end
    discrete_sbk_helper(probs, prefix_sum, i)
end

function discrete_sbk_helper(probs, prefix_sum, i)
    if i+1 == length(probs)
        DistUInt{num_bits+1}(i)
    else
        ifelse(
            flip(probs[i+1]/(last(prefix_sum) - prefix_sum[i+1])),
            DistUInt{num_bits+1}(i),
            discrete_sbk_helper(probs, prefix_sum, i + 1)
        )
    end
end

a = discrete_sbk([1/nbpow for _ in 1:nbpow])
b = discrete_sbk([1/nbpow for _ in 1:nbpow])

#~begin less
println(pr(a < b))
#~end

#~begin equals
println(pr(prob_equals(a, b)))
#~end

#~begin sum
println(expectation(a + b))
#~end