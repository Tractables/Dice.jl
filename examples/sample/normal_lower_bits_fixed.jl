using Revise
using Dice
using Distributions
using Plots

a = bitblast(DistFix{9, 0}, Normal(0, 1), 16, -8.0, 8.0)
code = @dice begin
            # observe(prob_equals(a.mantissa.number.bits[5:7], [false, false, false]))
            b = bitblast(DistFix{9, 0}, Normal(0, 1), 16, -8.0, 8.0)
            observe(prob_equals(a + b, DistFix{9, 0}(1.0)))
            a
end

# p = pr(a.mantissa.number.bits[5:7])

# plot(pr(a))

p = expectation(code)
plot(p)