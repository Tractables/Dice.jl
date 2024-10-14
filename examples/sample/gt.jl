using Dice
# using Random
using Distributions

NSAMPLES=100000
samples = rand(Bernoulli(0.5), NSAMPLES)
samples = map(x -> if x == 1 true else false end, samples)

function dice_program(s)
    code = @dice begin
            w = DistUInt{2}([flip(0.5), s])
            observe(w < DistUInt{2}([flip(0.5), flip(0.5)]))
            w
    end
    inside_expectation = expectation(code)
    prob_evidence = pr(allobservations(code))
    # @show prob_evidence
    return inside_expectation, prob_evidence[true]
end


mean = map(x -> dice_program(x), samples)

num = sum(map(x -> x[1]*x[2], mean))
den = sum(map(x -> x[2], mean))
print(num/den)

# true distribution ---- 0 -> 0.5, 1 -> 0.33, 2 -> 0.166, 3 -> 0
# true expectation ---- 0.66

