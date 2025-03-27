using Revise
using Alea
using Alea: num_flips, num_nodes, to_dice_ir

code = @dice_ite begin
    function discrete(p::Vector{Float64})
        mb = length(p)
        v = Vector(undef, mb)
        sum = 1
        for i=1:mb
            v[i] = p[i]/sum
            sum = sum - p[i]
        end

        # println(v)
        ans = DistInt(dicecontext(), mb-1)
        for i=mb-1:-1:1
            ans = if flip(v[i]) DistInt(dicecontext(), i-1) else ans end
        end
        return ans
    end

    function sendChar(key, observation)
        gen = discrete([0.5, 0.25, 0.125, 0.125])

        enc = key + gen
        d = prob_equals(observation, enc[1])
        return d
    end

    key = discrete([0.25, 0.25, 0.25, 0.25])
    d = true
    for i=1:4
        d&=sendChar(key, 2)
    end 
    key, d
end

# BDD analysis
bdd = compile(code)
infer(code, :bdd)
    

# IR analysis
# to_dice_ir(code)
# has_dice_binary() && rundice(code)
# has_dice_binary() && infer(code, :ocaml)