using Alea
using DelimitedFiles
using BenchmarkTools
using Plots


x = (@dice unit_gamma(DistFix{5, 4}, 2, -2.0))
a = x.returnvalue
b = reduce(&, x.observations)

dump_dot(a, filename="./mini-experiments/mixed-gamma/returnvalue.dot")
dump_dot(b, filename="./mini-experiments/mixed-gamma/observations.dot")