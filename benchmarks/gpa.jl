using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir
using Distributions
using StatsBase
using Distances

function gpa(p::Int, binbits::Int)
    code = @dice begin
        t = DistFixParam{binbits + 4, binbits}
        @show t
        d1 = continuous(dicecontext(), p, t, 4*Beta(8, 2))
        d2 = continuous(dicecontext(), p, t, 8*Beta(5, 5))
        # d1 = t(dicecontext(), 4.5)
        # d2 = t(dicecontext(), 4.5)
        
        gpa1 = if flip(0.95) d1 else 
                    if flip(0.15) t(dicecontext(), 4.0) else
                        t(dicecontext(), 0.0)
                    end
                end

        gpa2 = if flip(0.99) d2 else 
            if flip(0.1) t(dicecontext(), 8.0) else
                t(dicecontext(), 0.0)
            end
        end

        n = flip(0.25)
        final = if n gpa1 else gpa2 end
        o = prob_equals(final, t(dicecontext(), 2.5))
        Cond(n, o)
        # final
    end
    code
end

infer(gpa(2^24, 25), :bdd)


