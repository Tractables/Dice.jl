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

# collecting all y co and cg
terms = Vector(undef, 2^24)
for i = 1:2^24
    terms[i] = (prob_equals(y, Df(a[i, 4]))) & (prob_equals(co, Df(a[i, 5] + 128))) & (prob_equals(cg, Df(a[i, 6] + 128)))
end
@show 4

terms_y = Set{Float64}()
terms2 = Set{Float64}()
terms_co = Set{Float64}()
terms_cg = Set{Float64}()
for i = 1:2^24
    push!(terms_y, a[i, 4])
    push!(terms_co, a[i, 5] + 128)
    push!(terms_cg, a[i, 6] + 128)
end

for i = 1:2^10
    push!(terms2, (i-1)/4)
end

sd1 = setdiff(terms2, terms_y)
sd2 = setdiff(terms2, terms_co)
sd3 = setdiff(terms2, terms_cg)
@show 4


# collecting y
y_vals = zeros(2^10)
for i = 1:2^24
    y_vals[Int(a[Int(i), 4]*4) + 1] = 1
end

# collecting co
co_vals = zeros(2^10)
for i = 1:2^24
    co_vals[Int((a[Int(i), 5] + 128)*4) + 1] = 1
end

# collecting cg
cg_vals = zeros(2^10)
for i = 1:2^24
    cg_vals[Int((a[Int(i), 6] + 128)*4) + 1] = 1
end
@show 4

terms_y = Vector(undef, 2^10)
for i in 1:2^10
    if y_vals[i] == 1
        terms_y[i] = prob_equals(y, Df((i-1)/4))
    else
        terms_y[i] = false
    end
end

terms_co = Vector(undef, 2^10)
for i in 1:2^10
    if co_vals[i] == 1
        terms_co[i] = prob_equals(co, Df((i-1)/4))
    else
        terms_co[i] = false
    end
end

terms_cg = Vector(undef, 2^10)
for i in 1:2^10
    if cg_vals[i] == 1
        terms_cg[i] = prob_equals(cg, Df((i-1)/4))
    else
        terms_cg[i] = false
    end
end


for j in 9:-1:0
    @show j
    temp = Vector(undef, 2^j)
    for k in 1:2^j
        # @show 2*k - 1, 2*k
        # @show terms[1]
        temp[k] = terms_cg[2*k - 1] | terms_cg[2*k]
    end
    global terms_cg = temp
end 

@show 3
@show num_nodes(terms[1])

a = pr(@dice terms_y[1] && terms_co[1] && terms_cg[1])
pr(terms_co[1])
pr(terms_cg[1])


dump_dot(terms[1], filename="cg.dot")
