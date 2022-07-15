using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir
using Distributions
using StatsBase
using Distances

function lightspeed(p::Int, binbits::Int)
    
    code = @dice begin
        t = DistSigned{binbits + 6, binbits}
        t_2_m = DistSigned{binbits + 4, binbits}
        t_5 = DistSigned{binbits + 9, binbits + 5}
        t_res = DistSigned{2*binbits + 10, binbits}

        
        beta1 = uniform(dicecontext(), binbits + 6, t_res)
        sigma = uniform(dicecontext(), binbits + 5, t)
        
        data = [12.1374259163952, 26.6903103048018, 38.5878897957254, 30.4930667829189, 39.2801876119107,
        20.4174324499166, 25.7777563431966, 11.5919826316299, 37.3521894576722, 42.3729512347165,
        33.1974931235148, 18.3925621724044, 38.2093756620254, 26.5178923853568, 4.52268843482463,
        17.4645068462391, 20.0241067156045, 14.6755540100198, 12.9841025634912, 42.3191772083172,
        29.558684814201, 30.911111042245, 25.211786124301, 22.3592414735694, 30.7775798797013,
        16.8625137818992, 28.5736618568681, 19.5770593955495, 48.3010147870319, 31.2281915401234,
        21.601456892799, 29.6730840465467, 30.9093803330748, 17.5249474584363, 37.2377810832606,
        14.6787881367532, 24.770796317115, 34.6698348225234, 30.3842636610215, 24.5081046666978]
        
        obs = true
        for i = 1:length(data)
            #adding precision 5, adding bits (binbits + 6, 0)
            g1 = continuous(dicecontext(), p, t_5, Normal(0, 1), 0)
            g1 = add_bits(g1, binbits + 6, 0)

            term1 = t_res((g1.number * sigma.number)[1].bits[6:2*binbits + 15])
            term2 = beta1

            temp = (term1 + term2)[1]

            obs &= prob_equals(temp, t_res(dicecontext(), data[i]))
        end

        Cond(beta1, obs)
    end
    code
end


f = lightspeed(512, 0)
a = compile(f)
num_flips(a)
num_nodes(a)
a = 1
a = infer(f, :bdd)
a = expectation(f, :bdd)
a = variance(f, :bdd)