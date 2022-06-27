using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir
using Distributions
using StatsBase
using Distances

function example()
    
    code = @dice begin

        function next_obs_pos(l::DistFixParam{T, F})
            l_next, _ = if flip(1/2) 
                            (l1 + DistFixParam{5, 2}(dicecontext(), 1.0)) 
                        else 
                            (l1 - DistFixParam{5, 2}(dicecontext(), 1.0)) 
                        end
            o_next = l_next + uniform(dicecontext(), 2, DistFixParam{5, 2})
            return l_next, o_next
        end

        l1 = if flip(1/3) DistFixParam{5, 2}(dicecontext(), 2.0)
                else (if flip(1/2) DistFixParam{5, 2}(dicecontext(), 3.0)
                else DistFixParam{5, 2}(dicecontext(), 4.0)
                end)
            end 

        l2, o2 = next_obs_pos(l1)
        l3, o3 = next_obs_pos(l2)

        Cond(l1, prob_equals(o3[1], DistFixParam{5, 2}(dicecontext(), 6.5)))
    end
    code
end

f = example()
a = compile(f)
num_flips(a)
num_nodes(a)
a = 1
a = infer(f, :bdd)