###############
# R 0 to 256, G 0 to 256, B 0 to 256
# Y 0 to 256, Co -128 to 128, Cg -128 to 128
################

using Dice
using DelimitedFiles

flip_vector = [0.4223, 0.5149, 0.5034, 0.4998, 0.5028, 0.5022, 0.4991, 0.5006, 0.4899,
0.4949, 0.5289, 0.4707, 0.4723, 0.4743, 0.4785, 0.4835, 0.4887, 0.4920,
0.4949, 0.0010, 0.5320, 0.4679, 0.4681, 0.4692, 0.4706, 0.4746, 0.4786,
0.4837, 0.4915, 0.4949]

# Sanity Check 
# flip_vector = [0.5 for i in 1:30]
# flip_vector[20] = 0

y_flips = Vector(undef, 10)
co_flips = Vector(undef, 10)
cg_flips = Vector(undef, 10)

for i in 1:10
    y, co, cg = flip_vector[i], flip_vector[i+10], flip_vector[i+20]
    y_flips[i] = flip(y)
    co_flips[i] = flip(co)
    cg_flips[i] = flip(cg)
end

Df = DistFix{11, 2}

y = Df(vcat([false], y_flips))
co = Df(vcat([false], co_flips))
cg = Df(vcat([false], cg_flips))

@show 1

a = readdlm("support2.txt", '\t')
@show 2

terms = Vector(undef, 2^24)
for i = 1:2^24
    terms[i] = (prob_equals(y, Df(a[i, 1]))) & (prob_equals(co, Df(a[i, 2] + 128))) & (prob_equals(cg, Df(a[i, 3] + 128)))
end
@show 4
for j in 23:-1:0
    temp = Vector(undef, 2^j)
    @show j
    for k in 1:2^j
        temp[k] = terms[2*k - 1] | terms[2*k]
    end
    global terms = temp
end 

@show 3
# @show num_nodes(terms[1])
dump_dot(terms[1], filename="ycocg_2.dot")



@show pr(terms[1])