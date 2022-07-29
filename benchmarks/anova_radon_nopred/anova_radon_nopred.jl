using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir
using Distributions
using StatsBase
using Distances
using Plots

function anova_radon_nopred(p::Int, binbits::Int, flag::Int)
    
    code = @dice begin
        precision = 3

        data = [0.617007250574049, 0.895262019894671, -0.729874754380836,
        0.301471152630035, 0.929871984146596, 1.70686064033886, 1.09782179678289,
        1.27082634042846, 1.75132331738128, 1.03490015378005, 1.71226194303743,
        0.432311329644381, 1.04451460234109, 0.797605506723309, 1.19837496179441,
        2.00164115453824, -0.377675819779764, -0.148489586942737, 2.12586836175586,
        0.560257670828821, 0.751966977556745, 0.346571453512205, 1.2187492301484,
        1.56886622653154, 1.38035019540838, 2.76837231107256, 0.323735749142999,
        1.42941129934677, 0.468406777114355, 0.751905484130352, 0.568364441627544,
        0.0139444580475871, -0.152744699487943, 1.89057571718701, 1.48479996615007,
        1.87341593940818, 1.89344977488441, 0.537059334676276, 0.944371774385459,
        -0.474992028001801]

        t_s = DistSigned{binbits + 4 + precision, binbits + precision}
        t_g = DistSigned{binbits + 4 + precision, binbits + precision}
        t_a1 = DistSigned{binbits + 8, binbits}

        a1, _ = uniform(dicecontext(), binbits + 3, t_a1) - t_a1(dicecontext(), 4.0) # -4 to 4
        sigmay = uniform(dicecontext(), binbits + 3 + precision, t_s) # 0 to 8

        obs = true
        for i=1:length(data)
        # i = 1
            y = continuous(dicecontext(), p, t_g, Normal(0, 1), 0)
            y = Dice.trunc(y * sigmay, 2*precision + binbits)
            y, _ = y + a1
            obs &= prob_equals(y, t_a1(dicecontext(), data[i]))
        # end

        if flag == 0
            Cond(a1, obs)
        else
            Cond(sigmay, obs)
        end
        
        


        # t = DistSigned{binbits + 4, binbits}
        # t2 = DistSigned{binbits+2, binbits - 2}

        # a1 = (uniform(dicecontext(), binbits + 1, t2) + t2(dicecontext(), -4.0))[1] # -8 to 8
        # sigmay = uniform(dicecontext(), binbits + 3, t) # 0 to 8
        
        # data = [0.617007250574049, 0.895262019894671, -0.729874754380836,
        # 0.301471152630035, 0.929871984146596, 1.70686064033886, 1.09782179678289,
        # 1.27082634042846, 1.75132331738128, 1.03490015378005, 1.71226194303743,
        # 0.432311329644381, 1.04451460234109, 0.797605506723309, 1.19837496179441,
        # 2.00164115453824, -0.377675819779764, -0.148489586942737, 2.12586836175586,
        # 0.560257670828821, 0.751966977556745, 0.346571453512205, 1.2187492301484,
        # 1.56886622653154, 1.38035019540838, 2.76837231107256, 0.323735749142999,
        # 1.42941129934677, 0.468406777114355, 0.751905484130352, 0.568364441627544,
        # 0.0139444580475871, -0.152744699487943, 1.89057571718701, 1.48479996615007,
        # 1.87341593940818, 1.89344977488441, 0.537059334676276, 0.944371774385459,
        # -0.474992028001801]
        
        # obs = true
        # for i = 1:length(data)
        #     y1 = DistSigned{binbits + 2, binbits-2}(((add_bits(continuous(dicecontext(), p, DistSigned{binbits + 3, binbits}, Normal(0, 1)), binbits+5, 0) * add_bits(sigmay, binbits+4, 0))[1]).bits[binbits+3:2*binbits+4])
        #     y1 = (add_bits(y1, 1, 0) + add_bits(a1, 1, 0))[1]
        #     # y1 = (t((continuous(dicecontext(), p, t, Normal(0, 1)) * sigmay)[1]) + a1)[1]
        #     obs &= prob_equals(y1, DistSigned{binbits+3, binbits - 2}(dicecontext(), data[i]))
        # end
        # Cond(a1, obs)
        
    end
    code
end


f = anova_radon_nopred(32, 1, 0)
a = compile(f)
num_flips(a)
num_nodes(a)
b = infer(a)
c = b
plot(map(a -> a[1], c), map(a -> a[2], c))
expectation(a) + 0.25
variance(a)