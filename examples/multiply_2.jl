using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir
using Distributions
using StatsBase
using Distances

function unemployment(p::Int, binbits::Int)
    code = @dice begin
        t = DistSigned{binbits + 5, binbits}

        y = [3.33008960302557, 5.19543854472405, 5.88929762709886, 5.52449264517973, 5.31172037906861,
        7.1453284527505, 7.11693949967702, 10.2790569556659, 8.70290237657601, 4.91879758555161,
        5.9793649285972, 5.71069265888431, 5.82376740342438, 6.63877402512103, 7.42179960481787,
        9.62291014033926, 2.3662166776056, 5.13435595049398, 8.88839345256223, 4.82787281003398,
        6.66222539318123, 5.52684066394334, 5.1114875649346, 5.63288986028277, 4.38694756020315,
        5.57649838108011, 7.7437901545178, 3.97144535706026, 6.90655408345038, 5.34519996931202,
        5.82326082407921, 4.15702108539003, 6.81140925182179, 7.24764851401942, 5.49343534916886,
        8.28785318207118, 6.7638307279417, 4.90294078296499, 5.66570297954388, 5.20315542517743]

        y_lag = [4.3838241041638, 3.93442675489932, 7.57050890065729, 4.53683034032583, 5.28768584504724,
        7.84145292649045, 8.09962392030284, 9.55146255046129, 8.73574461648241, 4.44520985772833,
        4.86994492644444, 4.09735724627972, 4.01458069570362, 8.93653732435778, 6.37760733487085,
        9.47473778631538, 3.34918157150969, 5.00719783334061, 8.86413662843406, 4.86521017467603,
        6.06770903747529, 6.16693980395794, 7.25456838915125, 5.95538431135938, 5.22133663948625,
        5.36950460318476, 9.45933439927176, 4.04464610107243, 6.75704792523757, 4.24326258972287,
        6.9590606178157, 3.89350344482809, 5.34843717515469, 8.38955592149869, 5.99861560808495,
        8.28150384919718, 7.6049918634817, 5.4332405702211, 5.35873385947198, 5.18218877464533]

        beta1 = continuous(dicecontext(), p, t, Normal(1, 1), 0)
        beta2 = continuous(dicecontext(), p, t, Normal(1, 1), 0)
        sigma = add_bits(uniform(dicecontext(), 4, t), 0, 4)
        sigma = add_bits(t(dicecontext(), 2.0), 0, 2)

        # obs = true
        # for i=1:1
        #     a = continuous(dicecontext(), p, t, Normal(0, 1), 0) * sigma + beta1 + beta2*y_lag[i]
        #     obs &= prob_equals(a, t(dicecontext(), y[i]))
        # end

        # Cond(beta1, obs)
        # temp = (uniform(dicecontext(), 2, DistSigned{7, 0}) * sigma)[1]
        # final = t(temp.bits[4:binbits+7])
        
        # DistSigned{7, 2}((uniform(dicecontext(), 3, DistSigned{7, 1}) * DistSigned{7, 1}(dicecontext(), 2.0))[1])
        # a = uniform(dicecontext(), 2, DistSigned{7, 2})
        a = continuous(dicecontext(), p, DistSigned{7, 2}, Normal(0, 1), 0)
        b = DistSigned{6, 1}((DistInt(dicecontext(), 2) * a.number)[1].bits[2:7])
        b
        # DistSigned{7, 0}(((a.number * DistInt(dicecontext(), 2))[1]))
        # (DistInt(dicecontext(), 7) * add_bits(DistInt(dicecontext(), 2), 5))[1]
        # Cond(sigma, obs)
    end
    code
end

f = unemployment(16, 0)
compile(f)
a = infer(f, :bdd)
plot(map(a -> a[1], a), map(a -> a[2], a))
