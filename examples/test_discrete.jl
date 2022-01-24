using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir

code = @dice begin
    a = [0.33, 0.33, 0.34]
    function discrete(p::Vector{Float64})
        sum = 1
        a = flip(0.5)
        ans = ProbInt(a, 0)
        mb = length(p)
        for i = 0:mb-1
            ans = ifelse(prob_equals(ans, ProbInt(a, i)), 
                        ifelse(flip(p[i+1]/sum), ProbInt(a, i), ProbInt(a, i+1)), ans)
            sum = sum - p[i+1]
        end
        return ans
    end

    discrete(a)
end

bdd = compile(code)
num_flips(bdd)
num_nodes(bdd)
infer(code, :bdd)