using Dice
using DelimitedFiles



for bits in 3:8

    r_flips = Vector(undef, bits)
    g_flips = Vector(undef, bits)
    b_flips = Vector(undef, bits)

    y_flips = Vector(undef, bits)
    co_flips = Vector(undef, bits)
    cg_flips = Vector(undef, bits)

    for i in 1:bits
        r_flips[i], g_flips[i], b_flips[i] = flip(0.5), flip(0.5), flip(0.5)
        y_flips[i], co_flips[i], cg_flips[i] = flip(0.5), flip(0.5), flip(0.5)
    end

    # for i in 1:2
    #     y_flips[i + bits], co_flips[i + bits], cg_flips[i + bits] = flip(0.5), flip(0.5), flip(0.5)
    # end

 



    Df = DistFix{bits + 4, 2}
    red = Df([false, false, r_flips..., false, false])
    green = Df([false, false, g_flips..., false, false])
    blue = Df([false, false, b_flips..., false, false])

    y = [false, false, y_flips...]
    co = [false, false, co_flips...]
    cg = [false, false, cg_flips...]

    y_comp = (red/Df(4.0) + green/Df(2.0) + blue/Df(4.0)).mantissa.number.bits[1:bits+2]
    co_comp = (red - blue + Df(2.0^bits)).mantissa.number.bits[1:bits+2]
    cg_comp = (Df(0.0)-red/Df(2.0) + green - blue/Df(2.0) + Df(2.0^bits)).mantissa.number.bits[1:bits+2]

    final = prob_equals(y, y_comp) & prob_equals(co, co_comp) & prob_equals(cg,  cg_comp)
    @show bits, num_nodes(final)
    # @show pr(DistFix{bits+2, 0}(y_comp) >= DistFix{bits+2, 0}(0.0))
    # @show pr(DistFix{bits+2, 0}(co_comp) >= DistFix{bits+2, 0}(0.0))
    # @show pr(DistFix{bits+2, 0}(cg_comp) >= DistFix{bits+2, 0}(0.0))
end

dump_dot(final, filename = "rgb2ycc.dot")

final = red + green

y = DistUInt{bits + 1}([false, y_flips...])
co = DistUInt{bits + 1}([false, co_flips...])

eq = prob_equals(y, final) & prob_equals(co, red/DistUInt{bits + 1}(2) + green/DistUInt{bits + 1}(2))

num_nodes(eq)
dump_dot(eq, filename="rough.dot")




# b_flips = Vector(undef, 8)

# # The flip order is MSB to LSB interleaving between RGB
# for i in 1:8
#     r, g, b = flip_vector[i], flip_vector[i+8], flip_vector[i+16]
#     r_flips[i] = flip(r)
#     g_flips[i] = flip(g)
#     b_flips[i] = flip(b)
# end

# Df = DistFix{12, 2}

# red = Df([false, false, r_flips..., false, false])
# green = Df([false, false, g_flips..., false, false])
# blue = y = Df([false, false, b_flips..., false, false])

# y = Df([false, false, [flip(0.5) for i in 1:10]...])
# co = Df([false, false, [flip(0.5) for i in 1:10]...])
# cg = Df([false, false, [flip(0.5) for i in 1:10]...])

# final = prob_equals(y, red/Df(4.0) + green/Df(2.0) + blue/Df(4.0)) #& prob_equals(co, red/Df(2.0) - blue/Df(2.0) + Df(128.0)) & prob_equals(cg, green/Df(2.0) - red/Df(4.0) - blue/Df(4.0) + Df(128.0))

# pr(final)




# y = red/Df(4.0) + green/Df(2.0) + blue/Df(4.0)
# co = red/Df(2.0) - blue/Df(2.0) + Df(128.0)
# cg = green/Df(2.0) - red/Df(4.0) - blue/Df(4.0) + Df(128.0)

# y_reduce = reduce(&, y.mantissa.number.bits[4:12])
# co_reduce = reduce(&, co.mantissa.number.bits[3:11])
# cg_reduce = reduce(&, cg.mantissa.number.bits[4:12])

# pr(co_reduce)
# final = y_reduce & co_reduce & cg_reduce
# num_nodes(final)


# l = flip(0.3)
# pr(prob_equals(l, flip(0.5)) & prob_equals(l, flip(0.5)))

# a = readdlm("bitblast-pc/support.txt", '\t')
# terms = Vector(undef, 2^24)
# for i = 1:2^24
#     terms[i] = (prob_equals(y, Df(a[i, 1]))) & (prob_equals(co, Df(a[i, 2] + 128))) & (prob_equals(cg, Df(a[i, 3] + 128)))
# end

# for j in 23:-1:0
#     temp = Vector(undef, 2^j)
#     @show j
#     for k in 1:2^j
#         temp[k] = terms[2*k - 1] | terms[2*k]
#     end
#     global terms = temp
# end 

# dump_dot(terms[1], filename="bitblast-pc/ycocg.dot")