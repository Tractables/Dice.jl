using Revise
using Dice, Distributions
using DelimitedFiles
using BenchmarkTools
using Plots

function divide4(a::DistFix{W, F}) where {W, F}
    DFiP2 = DistFix{W + 2, F + 2}
    DFiP2(a.mantissa)
end

function divide2(a::DistFix{W, F}) where {W, F}
    DFiP2 = DistFix{W + 1, F + 1}
    DFiP2(a.mantissa)
end

function negate(a::DistFix{W, F}) where {W, F}
    DistFix{W, F}(0.0) - a
end

bits = 8
DFiP = DistFix{bits + 1, 0}
DFiP2 = DistFix{bits + 3, 2}

uni = n_unit_exponentials(DistFix{bits + 1, bits}, [0.0, 0.0, 0.0])
r = DistFix{bits+1, 0}(uni[1].mantissa)
g = DistFix{bits+1, 0}(uni[2].mantissa)
b = DistFix{bits+1, 0}(uni[3].mantissa)

y = divide4(r) + convert(DFiP2, divide2(g)) + divide4(b) 
co = divide2(r) + negate(divide2(b))
cg = negate(divide4(r)) + convert(DFiP2, divide2(g)) + negate(divide4(b))

a = pr((y, co, cg))

file = open("support.txt", "w")
for i in keys(a)
    writedlm(file, [i])
end

pr(co)
pr(cg)
length(pr(co))
minimum(pr(cg))
dump_dot(cg, filename="lt.dot")
