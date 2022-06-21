using Dice
using Dice: num_flips, num_nodes

a = [0.1, 0.2, 0.7]
function my_discrete(p::Vector{Float64})
    mb = length(p)
    v = Vector(undef, mb)
    sum = 1
    for i=1:mb
        v[i] = p[i]/sum
        sum = sum - p[i]
    end

    println(v)
    ans = DistInt(mb-1)
    for i=mb-1:-1:1
        ans = Dice.ifelse(flip(v[i]), DistInt(i-1), ans)
    end
    return ans
end      
d = my_discrete(a)

# bdd = compile(code)
# num_flips(bdd)
# num_nodes(bdd)
dist = infer(d)
@assert sum(values(dist)) ≈ 1
@assert dist[0] ≈ 0.1
@assert dist[1] ≈ 0.2
@assert dist[2] ≈ 0.7
