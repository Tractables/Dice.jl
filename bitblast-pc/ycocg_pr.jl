###############
# R 0 to 256, G 0 to 256, B 0 to 256
# Y 0 to 256, Co -128 to 128, Cg -128 to 128
################

using Dice
using DelimitedFiles

Df = DistFix{11, 2}
y, co, cg = n_unit_exponentials(DistFix{11, 10}, [0.0, 0.0, 0.0])
y = Df(y.mantissa)
co = Df(co.mantissa)
cg = Df(cg.mantissa)

@show 1

a = readdlm("support2.txt", '\t')
@show 2

terms = Vector(undef, 2^24)
for i = 1:2^24
    terms[i] = (prob_equals(y, Df(a[i, 4]))) & (prob_equals(co, Df(a[i, 5] + 128))) & (prob_equals(cg, Df(a[i, 6] + 128)))
end
@show 4
for j in 23:-1:0
    temp = Vector(undef, 2^j)
    @show j
    for k in 1:2^j
        # @show 2*k - 1, 2*k
        # @show terms[1]
        temp[k] = terms[2*k - 1] | terms[2*k]
    end
    global terms = temp
end 

@show 3
# @show num_nodes(terms[1])
dump_dot(terms[1], filename="ycocg.dot")



