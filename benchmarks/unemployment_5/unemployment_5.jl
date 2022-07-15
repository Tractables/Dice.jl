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

        y = [3.33008960302557, 5.19543854472405, 5.88929762709886, 5.52449264517973, 5.31172037906861]

        y_lag = [4.3838241041638, 3.93442675489932, 7.57050890065729, 4.53683034032583, 5.28768584504724]

        t_op = DistSigned{2*binbits+5, binbits}
        beta1 = add_bits(continuous(dicecontext(), p, DistSigned{binbits + 4, binbits}, Normal(1, 1), 0), binbits + 1, 0)
        beta2 = add_bits(continuous(dicecontext(), p, DistSigned{binbits + 6, binbits + 2}, Normal(1, 1), 0), 1, 0)
        sigma = uniform(dicecontext(), binbits + 4, t)

        obs = true
        for i=1:5
            a = add_bits(continuous(dicecontext(), p, DistSigned{binbits + 6, binbits + 3}, Normal(0, 1), 0), 2, 0)
            a_bits = add_bits(a, binbits + 5, 0)

            term1 = t_op((a_bits.number * sigma.number)[1].bits[5:2*binbits + 9])
            term2 = beta1

            b = t(dicecontext(), y_lag[1])
            beta2_bits = add_bits(beta2, binbits+5, 0) 
            term3 = t_op((beta2_bits.number * b.number)[1].bits[3:2*binbits+7]) 

            obs &= prob_equals(((term1 + term2)[1] + term3)[1], t_op(dicecontext(), y[i]))
        end

        Cond(sigma, obs)

        # Testing and experiments
        # term1
    end
    code
end

f = unemployment(8, 1)
b = compile(f)
num_nodes(b)
num_flips(b)
a = infer(b)
expectation(b) + 0.25
variance(f, :bdd)
# b = a[60:90]
plot(map(a -> a[1], a), map(a -> a[2], a))

gt_mean = [("beta[1]", 1.363409828), ("beta[2]", 0.7612146186), ("sigma", 0.928360085)]
gt_variance = [("beta[1]", 0.2140053728255653), ("beta[2]", 0.005274256728589788), ("sigma", 0.012279079516138264)]
