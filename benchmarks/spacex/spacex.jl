using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir
using Distributions
using StatsBase
using Distances
using Plots

function spacex(p::Int, binbits::Int)
    code = @dice begin
        t = DistFixParam{7+binbits, binbits}

        engines = continuous(dicecontext(), p, t, Normal(5, 1), false, false)
        first_stage = continuous(dicecontext(), p, t, Normal(10, 3), false, false)
        complted_first_stage, _ = engines + first_stage
        second_stage = continuous(dicecontext(), p, t, Normal(15, 3), false, false)
        completed_rocket, _ = complted_first_stage + second_stage

        completed_rocket
    end
    code
end


f = spacex(32, 6)
a = compile(f)
num_flips(a)
num_nodes(a)
b = infer(a)
c = b
plot(map(a -> a[1], c), map(a -> a[2], c))
expectation(a)
variance(a)

gt_a = 0.3300823875