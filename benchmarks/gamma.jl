using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir
using Distributions
using StatsBase
using Distances

function gammaTransform(p::Int, binbits::Int)
    
    code = @dice begin
        continuous(dicecontext(), p, DistFixParam{binbits+5, binbits}, Gamma(3, 1))
    end
    code
end

a = gammaTransform(1024*4, 12)
@time b = variance(a, :bdd)
