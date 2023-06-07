using Dice
using DelimitedFiles
using BenchmarkTools
using Plots 

DFiP = DistFixedPoint{16, 15}
code = @dice unit_gamma(DFiP, 3, -2.0)

code = unit_exponential(DistFixedPoint{15, 14}, -3.0)

plot(pr(code), xlabel="x", ylabel="pr(x)", title="14 bit blasted exponential(3)")
savefig("exp.png")

code = @dice unit_gamma(DistFixedPoint{4, 3}, 1, -3.0)
dump_dot(reduce(&, code.observations), filename="ineq.dot")