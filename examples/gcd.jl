using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir

code = @dice begin

    function uniform(bitrange::Int, bitwidth::Int)
        ans = fill(DistBool(dicecontext(), false), bitwidth)
        for i = 1:bitrange
            ans[i] = flip(0.5)
        end
        DistInt(ans)
    end

    function gcd(a::DistInt, b::DistInt)
        for _ = 1 : 1 + max_bits(b) ÷ log2(MathConstants.golden)
        # for _ = 1:8
            amb, _ = (a % b)
            # ambt = if prob_equals(amb, 0) 
            #         (if prob_equals(b, 1) DistInt(dicecontext(), 1) else DistInt(dicecontext(), 2) end) 
            #       else amb end
            # bt = if prob_equals(amb, 0) 
            #     (if prob_equals(b, 1) DistInt(dicecontext(), 1) else DistInt(dicecontext(), 2) end) 
            #   else b end
            # b, a = ambt, bt

            amb = if prob_equals(amb, 0) b else amb end
            b, a = amb, b
            
        end
        return a
    end

    n = 9
    a, _ = uniform(n, n+1) + 1
    b, _ = uniform(n, n+1) + 1
    g = gcd(a, b)
    # prob_equals(g, 1)
    g
end

# BDD analysis
# bdd = compile(code)
# num_flips(bdd), num_nodes(bdd)
# infer(code, :bdd)

function execute(code)
    @time infer(code, :bdd)
end

execute(code)