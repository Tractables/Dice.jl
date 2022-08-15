using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir
using Distributions
using StatsBase
using Distances
using Plots

function anova_radon_nopred(p::Int, binbits::Int, flag::Int)
    
    code = @dice begin

        function observe_normal2(a::DistSigned{T1, F1}, b::DistSigned{T2, F2}, datapt, g, bits, p) where T1 where F1 where T2 where F2
            # @show T1 F1 T2 F2
            a_start = -2^(T1 - F1 - 1)
            a_end = 2^(T1 - F1 - 1)

            b_start = -2^(T2 - F2 - 1)
            b_start = 0
            b_end = 2^(T2 - F2 - 1)

            expression = false

            y = Dice.trunc(g * b, p + bits)
            y, _ = y + a
            e1 = ((!prob_equals(a, DistSigned{T1, F1}(dicecontext(), datapt))
            || !prob_equals(b, DistSigned{T2, F2}(dicecontext(), 1/2^(F2))))
            & prob_equals(y, DistSigned{T1, F1}(dicecontext(), datapt)))

            e2 = (prob_equals(a, DistSigned{T1, F1}(dicecontext(), datapt)) 
            & prob_equals(b, DistSigned{T2, F2}(dicecontext(), 1/2^(F2)))
            & flip(pdf(Normal(datapt, 1/2^(F2)), datapt)*10^(-5)))

            expression |= (e1 || e2)
            expression
        end

        function observe_normal(a::DistSigned{T1, F1}, b::DistSigned{T2, F2}, datapt) where T1 where F1 where T2 where F2
            # @show T1 F1 T2 F2
            a_start = -2^(T1 - F1 - 1)
            a_end = 2^(T1 - F1 - 1)

            b_start = -2^(T2 - F2 - 1)
            b_start = 0
            b_end = 2^(T2 - F2 - 1)

            expression = false
            for i=1:2^(T1)
                for j=1:2^(T2 - 1)
                    a_val = a_start + (i-1)/2^(F1)
                    b_val = b_start + (j-1)/2^F2
                    flip_prob = pdf(Normal(a_val, b_val), datapt)*10^(-3)
                    @show a_val, b_val
                    expression |= (prob_equals(a, DistSigned{T1, F1}(dicecontext(), a_val))
                                    & prob_equals(b, DistSigned{T2, F2}(dicecontext(), b_val))
                                    & flip(flip_prob))

                end
            end
            expression
        end

        precision = 3

        data = [0.617007250574049]

        t_s = DistSigned{binbits + 4, binbits}
        t_g = DistSigned{binbits + 4 + precision, binbits + precision}
        # t_a1 = DistSigned{binbits + 3, binbits}
        t_a1 = DistSigned{binbits + 8, binbits}

        a1, _ = uniform(dicecontext(), binbits + 3, t_a1) + t_a1(dicecontext(), -4.0) # -4 to 4
        sigmay = uniform(dicecontext(), binbits + 3, t_s) # 0 to 8

        obs = true
        y = continuous(dicecontext(), p, t_g, Normal(0, 1), 0, 0)
        obs &= observe_normal2(a1, sigmay, data[1], y, binbits, precision)
        # # for i=1:length(data)
        # i = 1
        #     y = continuous(dicecontext(), p, t_g, Normal(0, 1), 0, 0)
        #     y = Dice.trunc(y * sigmay, precision + binbits)
        #     y, _ = y + a1
        #     obs &= prob_equals(y, (t_a1(dicecontext(), data[i]) - a1)[1]/sigmay)
        # end

        if flag == 0
            Cond(a1, obs)
        else
            Cond(sigmay, obs)
        end
        
    end
    code
end


f = anova_radon_nopred(1, 5, 0)
a = compile(f)
num_flips(a)
num_nodes(a)
b = infer(a)
c = b
plot(map(a -> a[1], c), map(a -> a[2], c))
expectation(a)
variance(a)

gt_a = 0.3300823875