using Dice
using Dice: num_flips, num_nodes, to_dice_ir

code = @dice begin
    a = [0.1, 0.2, 0.7]
    function discrete(p::Vector{Float64})
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
            ans = if flip(v[i]) DistInt(i-1) else ans end
        end
        return ans
    end      
    discrete(a)
end 

bdd = compile(code)
num_flips(bdd)
num_nodes(bdd)
dist = infer(bdd)
@assert sum(dist) ≈ 1
@assert dist[1] ≈ 0.1
@assert dist[2] ≈ 0.2
@assert dist[3] ≈ 0.7
