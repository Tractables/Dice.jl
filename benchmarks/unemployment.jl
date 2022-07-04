using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir
using Distributions
using StatsBase
using Distances

function unemployment(p::Int, binbits::Int)
    code = @dice begin
        t = DistSigned{binbits + 5, binbits}
        t_mp = DistSigned{binbits + 7, binbits+2}

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

        t_op = DistSigned{2*binbits+5, binbits}
        beta1 = add_bits(continuous(dicecontext(), p, DistSigned{binbits + 4, binbits}, Normal(1, 1), 0), binbits + 1, 0)
        beta2 = add_bits(continuous(dicecontext(), p, DistSigned{binbits + 6, binbits + 2}, Normal(1, 1), 0), 1, 0)
        sigma = uniform(dicecontext(), binbits + 2, t)

        obs = true
        for i=1:1
            a = add_bits(continuous(dicecontext(), p, DistSigned{binbits + 5, binbits + 2}, Normal(0, 1), 0), 2, 0)
            a_bits = add_bits(a, binbits + 5, 0)

            term1 = t_op((a_bits.number * sigma.number)[1].bits[3:2*binbits + 7])
            term2 = beta1

            b = t(dicecontext(), y_lag[1])
            beta2_bits = add_bits(beta2, binbits+5, 0) 
            term3 = t_op((beta2_bits.number * b.number)[1].bits[3:2*binbits+7]) 

            obs &= prob_equals(((term1 + term2)[1] + term3)[1], t_op(dicecontext(), y[i]))
        end

        Cond(beta2, obs)

        # Testing and experiments
        # beta1
    end
    code
end

f = unemployment(1, 3)
b = compile(f)
num_nodes(b)
num_flips(b)
a = infer(f, :bdd)
expectation(f, :bdd)
variance(f, :bdd)
plot(map(a -> a[1], a), map(a -> a[2], a))
