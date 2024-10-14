using Revise
using Dice
# using Random
using Distributions

NSAMPLES=1000
samples = rand(Bernoulli(0.5), NSAMPLES)
samples = map(x -> if x == 1 true else false end, samples)

pws = Dict{}(0 => 0.4, 1 => 0.6)

function dice_program(s)
    param = if s 2/3 else 3/4 end
    # param = 0.7
    code = @dice begin
            flip1 = flip(param)
            # flip2 = if flip1 flip(4/7) else flip(2/3) end
            flip2 = s
            w = DistUInt{2}([flip1, flip2])
            observe(w < DistUInt{2}([flip(0.5), flip(0.5)]))
            w
    end
    inside_expectation = expectation(code)
    prob_evidence = pr(allobservations(code))
    # @show prob_evidence
    return inside_expectation, prob_evidence[true], pws[s]
end


mean = map(x -> dice_program(x), samples)

num = sum(map(x -> x[1]*x[2]*x[3]/0.5, mean))
den = sum(map(x -> x[2]*x[3]/0.5, mean))
print(num/den)

# true distribution ---- 0 -> 0.1, 1 -> 0.2, 2 -> 0.3, 3 -> 0.4
# true expectation ---- 1