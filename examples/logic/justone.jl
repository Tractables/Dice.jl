include("cudd_lite.jl")


function only_one(bs)
    onlys = []
    for i in 1:count
        x = tru
        for j in 1:count
            x &= eq(bs[j], i==j)
        end
        push!(onlys, x)
    end
    reduce(|, onlys)
end




countlog2 = 3

bs = [choice() for _ in 1:2^countlog2]

dump_dot(only_one(bs), "x.dot")

bs = []
choices = [choice() for _ in 1:countlog2]
for i in 0:2^countlog2 - 1
    bits = [(i >> biti) & 1 == 1 for biti in 0:countlog2 - 1]
    push!(bs, reduce(&, [eq(c, b) for (c, b) in zip(choices, bits)]))
end
dump_dot(only_one(bs), "y.dot")

