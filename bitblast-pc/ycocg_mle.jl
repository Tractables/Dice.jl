using Dice
using DelimitedFiles

mle_params = open("bitblast-pc/mle_params.txt", "r")
a = readlines(mle_params)
close(mle_params)

#Flip vector consist of all flips of Y then all flips of Co, then Cg from LSB to MSB
flip_vector = Vector(undef, 30)
for i in 1:30
    flip_vector[i] = parse(Float64, a[i])
end

y_flips = Vector(undef, 10)
co_flips = Vector(undef, 10)
cg_flips = Vector(undef, 10)

# The flip order is LSB to MSB interleaving between Y, Co and Cg
for i in 1:10
    y, co, cg = flip_vector[i], flip_vector[i+10], flip_vector[i+20]
    y_flips[10 - i + 1] = flip(y)
    co_flips[10 - i + 1] = flip(co)
    cg_flips[10 - i + 1] = flip(cg)
end

Df = DistFix{11, 2}

y = Df(vcat([false], y_flips))
co = Df(vcat([false], co_flips))
cg = Df(vcat([false], cg_flips))

a = readdlm("bitblast-pc/support.txt", '\t')
terms = Vector(undef, 2^24)
for i = 1:2^24
    terms[i] = (prob_equals(y, Df(a[i, 1]))) & (prob_equals(co, Df(a[i, 2] + 128))) & (prob_equals(cg, Df(a[i, 3] + 128)))
end

for j in 23:-1:0
    temp = Vector(undef, 2^j)
    @show j
    for k in 1:2^j
        temp[k] = terms[2*k - 1] | terms[2*k]
    end
    global terms = temp
end 

@show pr(terms[1])[true]
#0.03148561282174933