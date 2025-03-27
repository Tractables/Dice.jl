using Alea
using Alea: num_flips, num_nodes

for n = 7:7
    code = @dice_ite begin

        function uniform(bitrange::Int, bitwidth::Int)
            ans = fill(DistBool(dicecontext(), false), bitwidth)
            for i = 1:bitrange
                ans[i] = flip(0.5)
            end
            DistInt(ans)
        end

        function gcd(a::DistInt, b::DistInt)
            for _ = 1 : 1 + max_bits(b) ÷ log2(MathConstants.golden)
                t = b
                converged = prob_equals(b, 0)
                amb, _ = (a % b)
                b = if converged
                        b
                    else
                        amb
                    end
                a = if converged
                        a
                    else
                        t
                    end
            end
            return a
        end

        a, _ = uniform(n, n+1) + 1
        b, _ = uniform(n, n+1) + 1
        g = gcd(a, b)
        prob_equals(g, 1)
    end

    @show n
    @show 2^n
    
    bdd = compile(code)
    @show num_flips(bdd)
    @show num_nodes(bdd)

    @time @show infer(code, :bdd)
end
