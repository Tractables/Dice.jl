using Revise
using Dice
using Random
using Distributions

# with observe
bits = 2
pieces = 2^(bits + 4)
DFiP = DistFix{6 + bits, bits}
code = @dice begin
    w1 = bitblast(DFiP, Normal(0, sqrt(2)), pieces, -8.0, 8.0)
    observe(prob_equals(w1.mantissa.number.bits[5+bits:6+bits], [true, false]))
    w1
end
p1 = pr(code)
num_nodes(code.returnvalue)
plot(p1)

# without observe
bits = 0
pieces = 2^(bits + 3)
DFiP = DistFix{6 + bits, bits}
code = @dice begin
    w1 = bitblast_sample(DFiP, Normal(0, sqrt(2)), pieces, -8.0, 8.0, 0.5, 0.25)
    # observe(prob_equals(w1.mantissa.number.bits[5+bits:6+bits], [true, true]))
    DistFix{8, 2}([w1.mantissa.number.bits..., true, false])
end
p2 = pr(code)
plot!(p2)
num_nodes(code.returnvalue)
