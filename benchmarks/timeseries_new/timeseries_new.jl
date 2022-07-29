using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir
using Distributions
using StatsBase
using Distances

function timeseries(p::Int, binbits::Int, flag::Int)
    code = @dice begin
        t = DistSigned{binbits + 4, binbits}
        t_1 = DistSigned{binbits + 5, binbits + 1}
        t_3 = DistSigned{binbits + 7, binbits + 3}
        t_res = DistSigned{binbits + 8, binbits}

        # x [-2, 2] y [-8, 8]
        x = [0.0530897649405518, -0.427176340746955, 0.575506045064776, -1.05503057032362, -0.00138425373659317, 0.362367184144129, -0.906400668762085, 1.39464604836768, -1.40047244298115, -0.872458836353285, -0.425555167755021, -0.192907289991263, 0.611345320709905, 0.223493915844394, -0.335855643300744, -0.786177511979181, 1.0466888412128, -1.35578280849525, -0.4802662607177, -0.482825573577857, -0.44808934155094, 1.41677018342172, -1.12722529948411, -1.52518755310289, -0.232336215009525, -0.452482201859223, -0.235580964484178, -0.789514125170731, 1.61944620303219, 0.735756130006795, -1.0253656503392, 0.936124304383727, 1.10587169595422, 0.833182124741184, 0.113696178051401, -1.15636049024915, 1.85507312756962, 1.30957252757083, 0.822235075588577, -1.43800316565635]
        y = [-1.09070023335653, -2.49513228748069, -2.07918898737732, -3.34621083464711, -3.21905761756761, -3.84835139936697, -4.14591579938845, -2.17085702918779, -2.72986009710348, -2.35417403593087, -3.05798313015489, -2.85360404455837, -2.9261492993768, -2.67713444957349, -2.97731974867721, -4.7510500052692, -3.2939903406896, -4.11626048191435, -4.08086402479665, -3.34743297842617, -3.59294970060833, -1.70489370379594, -3.522911840642, -4.13944648650588, -4.04992280586435, -3.71707285571859, -2.6830205191276, -3.21920265745786, -1.78221835462429, -1.71385611701893, -3.15284681754168, -3.26094915407183, -2.92240028325557, -2.40186352631743, -3.1697331801915, -4.00540748111558, -2.32625323220302, -1.74827635320394, -1.05716214917384, -3.44536781268663]
        termg = Vector(undef, length(x) - 1)
        for i = 1:length(y) - 1
            termg[i] = continuous(dicecontext(), p, t, Normal(0, 0.5), 0)
        end

        alpha = (uniform(dicecontext(), binbits + 3, t) - t(dicecontext(), 4.0))[1]

        # adding precision 1, adding bits (binbits + 4, 0)
        beta = (uniform(dicecontext(), binbits + 3 + 1, t_1) - t_1(dicecontext(), 4.0))[1]

        # adding precision 3, adding bits bits (binbits + 4, 0)
        lambda = uniform(dicecontext(), binbits + 3, t_3)

        obs = true
        for i = 2:length(x)
            term1 = add_bits(termg[i-1], 4, 0)
            # term1 = add_bits(continuous(dicecontext(), p, t, Normal(0, 0.5), 0), binbits + 4, 0)
            term2 = add_bits(alpha, 4, 0)
            # print(length((beta.number *  t(dicecontext(), x[i]).number)[1].bits[2:9]))
            # @show 2*binbits + 9
            # term3 = t_res((beta.number *  t(dicecontext(), x[i]).number)[1].bits[2:2*binbits + 9])
            term3 = Dice.trunc(beta * t_1(dicecontext(), x[i]), binbits + 2*1)
            # @show typeof(term3)
            # term4 = t_res((lambda.number * t(dicecontext(), y[i-1]).number)[1].bits[4:2*binbits + 11])
            term4 = Dice.trunc(lambda * t_3(dicecontext(), y[i-1]), binbits + 2*3)
            # @show typeof(term4)
            temp = (((term3 + term4)[1] + term2)[1] + term1)[1]

            obs &= prob_equals(temp, t_res(dicecontext(), y[i]))
        end

        if flag == 0
            Cond(alpha, obs)
        elseif flag == 1
            Cond(beta, obs)
        else
            Cond(lambda, obs)
        end
    end
    code
end

f = timeseries(1, 1)
b = compile(f)
num_nodes(b)
num_flips(b)
a = infer(f, :bdd)
expectation(f, :bdd)
variance(f, :bdd)
plot(map(a -> a[1], a), map(a -> a[2], a))