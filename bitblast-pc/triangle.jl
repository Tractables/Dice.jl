using Dice
using Plots

t = DistFix{7, 6}
code = @dice begin
            n1, n2 = n_unit_exponentials(t, [0.0, 0.0])
            observe(n1 < n2)
            n2
end

# Verifying probability distribution
a = pr(code)
plot(a)

# Plotting BDD
b = reduce(&, code.observations)
dump_dot(DistUInt{7}([(b & i) for i in code.returnvalue.mantissa.number.bits]), filename="triangleBDD.dot")