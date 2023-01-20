include("cudd_lite.jl")

pre = choice()
x = [choice() for _ in 1:6]
post = choice()

res = x[1] & x[2] | x[3] & x[4] | x[5] & x[6]

res = (x[1] | x[2]) & (x[3] | x[4]) & (x[5] | x[6])
dump_dot(res, "good.dot")
dump_dot(pre & res, "pre_good.dot")
dump_dot(post & res, "post_good.dot")


res = (x[1] | x[4]) & (x[2] | x[5]) & (x[3] | x[6])
dump_dot(res, "bad.dot")
dump_dot(pre & res, "pre_bad.dot")
dump_dot(post & res, "post_bad.dot")

123456
135246



crux = pre
a = crux & (x[1] | x[3])
b = !crux & (x[2] | x[4])

dump_dot([a, b, a & b], "ya.dot")

a = false
b = false
if crux
    if x1 | x3
        a = true
    end
else
    if x2 | x4
        b = true
    end
end

# maybe for "bad" BDDs we could use some that are exponential regardless of
# order, e.g. middle bit of multiplication
# https://en.wikipedia.org/wiki/Binary_decision_diagram



