using Dice
using DelimitedFiles

flip_vector = [0.5 for i in 1:27]

y_flips = Vector(undef, 9)
co_flips = Vector(undef, 9)
cg_flips = Vector(undef, 9)

# The flip order is LSB to MSB interleaving between Y, Co and Cg
for i in 1:9
    y, co, cg = flip_vector[i], flip_vector[i+9], flip_vector[i+18]
    y_flips[9 - i + 1] = flip(y)
    co_flips[9 - i + 1] = flip(co)
    cg_flips[9 - i + 1] = flip(cg)
end

Df = DistFix{10, 0}

y = Df([false, y_flips...])
co = Df([false, co_flips...])
cg = Df([false, cg_flips...])
y.mantissa.number.bits[2] = false

a = readdlm("bitblast-pc/ycocgr/support.txt", '\t')
terms = Vector(undef, 2^24)
for i = 1:2^24
    terms[i] = (prob_equals(y, Df(a[i, 1]))) & (prob_equals(co, Df(a[i, 2] + 256))) & (prob_equals(cg, Df(a[i, 3] + 256)))
end

for j in 23:-1:0
    temp = Vector(undef, 2^j)
    @show j
    for k in 1:2^j
        temp[k] = terms[2*k - 1] | terms[2*k]
    end
    global terms = temp
end 

dump_dot(terms[1], filename="bitblast-pc/ycocgr/ycocgr.dot")