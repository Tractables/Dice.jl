using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir
using Distributions
using StatsBase
using Distances

function gauss_mix_asym_prior(p::Int, binbits::Int)
    code = @dice begin
        t = DistSigned{binbits + 4, binbits}
        t_2 = DistSigned{binbits + 6, binbits + 2}
        t_res = DistSigned{binbits + 8, binbits}

        # y [-4.4 4.8]
        y = [-4.42240141499726, -2.38254474811358, 4.46003506755005, -2.06779349559439,
        -1.90472822115053, -1.38063238393424, 2.4560053700776, -2.16525118775164, 3.59283111997059,
        -1.37514949864802, 3.11791541978786, -2.42680944749416, -3.09428403855117, -3.20476382063687,
        -3.85911355416889, -1.96099930226549, -1.67053823688585, 1.65153535395172, -2.46498438286183,
        2.47088045459675, -1.90793566789462, 1.93824458416405, -3.48517985531111, 2.67535752442589,
        -2.41176963566931, -2.40341346381303, 4.35578782060231, -4.02895296743614, 3.24060045335942,
        4.86808301156485, -4.27450050279819, -3.05934862717024, -2.4565573123528, -0.9853565693853,
        -2.40261773102976, -3.70834615526765, 3.35828117133431, -2.05032748483516, -3.50293429413932,
        4.4317800899911]

        mu1 = continuous(dicecontext(), p, t, Normal(2.75, 0.5), 0)
        mu2 = continuous(dicecontext(), p, t, Normal(-2.75, 0.5), 0)
        sigma1 = uniform(dicecontext(), binbits + 2, t)
        sigma2 = uniform(dicecontext(), binbits + 2, t)

        obs = true
        for i = 1:length(y)
            a = flip(0.3)

            #adding precision 2, adding bits (binbits + 4, 0)
            g1 = continuous(dicecontext(), p, t_2, Normal(0, 1), 0)
            temp1 = (Dice.trunc(g1 * sigma1, 2 + binbits) + add_bits(mu1, 4, 0))[1]
            # temp1 = (t_res((g1.number * sigma1.number)[1].bits[3:2*binbits + 10]) + mu1)[1]

            #adding precision 2, adding bits (binbits + 4, 0)
            g2 = continuous(dicecontext(), p, t_2, Normal(0, 1), 0)
            temp2 = (Dice.trunc(g2 * sigma2, 2 + binbits) + add_bits(mu2, 4, 0))[1]
            # temp2 = (t_res((g2.number * sigma2.number)[1].bits[3:2*binbits + 10]) + mu2)[1]

            obs &= prob_equals(if a temp1 else temp2 end, t_res(dicecontext(), y[i]))
        end

        Cond(mu1, obs)
    end
    code
end

f = gauss_mix_asym_prior(16, 1)
b = compile(f)
num_nodes(b)
num_flips(b)
a = infer(f, :bdd)
expectation(f, :bdd)
variance(f, :bdd)