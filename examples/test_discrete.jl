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
        ans = ProbInt(mb-1)
        for i=mb-1:-1:1
            ans = if flip(v[i]) ProbInt(i-1) else ans end
        end
        return ans
    end

    # function discrete2(p::Vector{Float64})
    #     mb = length(p)
    #     sum = 1
    #     ans = ProbInt(0, flip(0.5))
    #     for i = 0:mb-1
    #         ans = if prob_equals(ans, i)
    #                     if flip(p[i+1]/sum)
    #                         ProbInt(i, flip(0.5))
    #                     else
    #                         ProbInt(i+1, flip(0.5))
    #                     end
    #                 else 
    #                     ProbInt(i, flip(0.5))
    #                 end
    #         sum = sum - p[i+1]
    #     end
    #     return ans
    # end        
    discrete(a)
end

bdd = compile(code)
num_flips(bdd)
num_nodes(bdd)
infer(code, :bdd)