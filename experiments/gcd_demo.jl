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

    function dice_gcd(a, b)
        for _ = 0 : 10
            gt = a > b
            lt = b > a
            amb, _ = a - b
            bma, _ = b - a
            a = if gt amb else a end
            b = if lt bma else b end
        end
        return a
    end

    function gcd(a::DistInt, b::DistInt)
        for _ = 1 : 1 + max_bits(b) ÷ log2(MathConstants.golden)
        # for _ = 1:1 + 5*max_bits(b)
            amb, _ = (a % b)
            amb = if prob_equals(amb, 0) b else amb end
            b, a = amb, b
        end
        return a
    end

    n = 11
    a, _ = uniform(n, n+1) + 1
    b, _ = uniform(n, n+1) + 1
    g = gcd(a, b)
    # prob_equals(g, 1)
    g
end

# BDD analysis
bdd = compile(code)
num_flips(bdd), num_nodes(bdd)
infer(code, :bdd)