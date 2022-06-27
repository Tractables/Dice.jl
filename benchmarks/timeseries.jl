using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir
using Distributions
using StatsBase
using Distances

function altermu(p::Int, binbits::Int)
    
    code = @dice begin
        t = DistSigned{binbits + 5, binbits}
        # a1 = Vector{DistBool}(undef, binbits+5)
        # a2 = Vector{DistBool}(undef, binbits+5)
        # for i=1:binbits+4
        #     a1[i] = flip(0.5)
        #     a2[i] = flip(0.5)
        # end
        # a1[binbits+5] = flip(0)
        # a2[binbits+5] = flip(0)
        # mu2 = (t(a1) + t(dicecontext(), -8.0))[1]
        # mu1 = (t(a2) + t(dicecontext(), -8.0))[1]

        mu1 = (uniform(dicecontext(), binbits + 4, t) + t(dicecontext(), -8.0))[1]
        mu2 = (uniform(dicecontext(), binbits + 4, t) + t(dicecontext(), -8.0))[1]
        
        data = [-2.57251482,  0.33806206,  2.71757796,  1.09861336,  2.85603752,
        -0.91651351,  0.15555127, -2.68160347,  2.47043789,  3.47459025,
        1.63949862, -1.32148757,  2.64187513,  0.30357848, -4.09546231,
        -1.50709863, -0.99517866, -2.0648892 , -2.40317949,  3.46383544,
        0.91173696,  1.18222221,  0.04235722, -0.52815171,  1.15551598,
        -1.62749724,  0.71473237, -1.08458812,  4.66020296,  1.24563831,
        -0.67970862,  0.93461681,  1.18187607, -1.49501051,  2.44755622,
        -2.06424237, -0.04584074,  1.93396696,  1.07685273, -0.09837907]
        
        # a = (mu2 + mu1)[1]
        obs = true
        for i = 1:length(data)
            # @show data[i]
            y1 = ((mu2 + mu1)[1] + continuous(dicecontext(), p, t, Normal(0, 1)))[1]
            obs &= prob_equals(y1, t(dicecontext(), data[i]))
        end
        Cond(mu2, obs)
        # (mu1 + mu2)[1]
    end
    code
end

f = altermu(32, 1)
a = compile(f)
num_flips(a)
num_nodes(a)
a = 1
@time a = infer(f, :bdd)