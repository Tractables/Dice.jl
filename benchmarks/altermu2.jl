using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir
using Distributions
using StatsBase
using Distances

function altermu(p::Int, binbits::Int, b::Bool, b2::Bool)
    
    code = @dice begin
        t = DistSigned{binbits + 5, binbits}

        data = [-2.57251482,  0.33806206,  2.71757796,  1.09861336,  2.85603752,
        -0.91651351,  0.15555127, -2.68160347,  2.47043789,  3.47459025,
        1.63949862, -1.32148757,  2.64187513,  0.30357848, -4.09546231,
        -1.50709863, -0.99517866, -2.0648892 , -2.40317949,  3.46383544,
        0.91173696,  1.18222221,  0.04235722, -0.52815171,  1.15551598,
        -1.62749724,  0.71473237, -1.08458812,  4.66020296,  1.24563831,
        -0.67970862,  0.93461681,  1.18187607, -1.49501051,  2.44755622,
        -2.06424237, -0.04584074,  1.93396696,  1.07685273, -0.09837907]
        gaussians = Vector(undef, length(data))
        for i=1:length(data)
            gaussians[i] = add_bits(continuous(dicecontext(), p, t, Normal(0, 1), b, b2), 2, 0)
        end
        mu1 = add_bits((uniform(dicecontext(), binbits + 4, t) + t(dicecontext(), -8.0))[1], 2, 0)
        mu2 = add_bits((uniform(dicecontext(), binbits + 4, t) + t(dicecontext(), -8.0))[1], 2, 0)
        

        
        a = (mu2 + mu1)[1]
        obs = true
        for i = 1:length(data)
            # y1, y2 = ((mu2 + mu1)[1] + continuous(dicecontext(), p, t, Normal(0, 1), b, b2))
            y1 = (a + gaussians[i])[1]
            obs &= prob_equals(y1, DistSigned{binbits + 7, binbits}(dicecontext(), data[i]))
            # obs &= y2
        end
        obs
        # # (
        #     add_bits(continuous(dicecontext(), p, t, Normal(0, 1), b, b2), 1, 0) 
            # + 
            # add_bits(mu2, 1, 0))[2]
        # (continuous(dicecontext(), p, t, Normal(0, 1), b, b2) + mu2)[1]
        # ((mu2) + continuous(dicecontext(), p, t, Normal(0, 1), b, b2))[1]
        # y1
        # y1 = (mu2 + continuous(dicecontext(), p, t, Normal(0, 1), b, b2))[1]
        # prob_equals(y1, t(dicecontext(), data[2]))

        # obs
        # a = add_bits(continuous(dicecontext(), p, t, Normal(0, 1), b, b2), 1, 0)
        # b = add_bits(mu2, 1, 0)
        # y1, y2 = (continuous(dicecontext(), p, t, Normal(0, 1), b, b2) + mu2)
        # (a + b)[1]

        # mu2 = uniform(dicecontext(), 1, DistFixParam{3, 0})
        # g = continuous(dicecontext(), p, DistFixParam{5, 0}, Normal(3, 1), b, b2)
        # # mu2 = DistFixParam{2, 0}(dicecontext(), 0.0)
        # # Cond((mu2 + continuous(dicecontext(), p, DistFixParam{2, 0}, Normal(0, 1), b, b2))[1], prob_equals(mu2, DistFixParam{2, 0}(dicecontext(), 0.0)))
        # # y = (mu2 + g)[1]
        # # prob_equals(y, DistFixParam{5, 2}(dicecontext(), 0.0))
        # g



    end
    code
end


for i = 0:4
    f = altermu(2^i, 0, false, false)
    @show expectation(f, :bdd)
end

infer(altermu(16, 0, false, false), :bdd)
pieces = 8
bits = 0

f1 = altermu(pieces, bits, false, true)
f2 = altermu(pieces, bits, false, false)
@assert infer(f1, :bdd) == infer(f2, :bdd)

f = altermu(pieces, bits, false, true)
infer(f, :bdd)

pieces = 16
bits = 0
f = altermu(pieces, bits, false, false)
a = compile(f)
num_flips(a)
num_nodes(a)
expectation(a)
infer(f, :bdd)
dump_dot(a, "rough.dot")

pieces = 4
bits = 0
f2 = altermu(pieces, bits, false, false)
a2 = compile(f2)
num_flips(a2)
num_nodes(a2)
expectation(a2)
dump_dot(a2, "rough2.dot")

dump_dot(a, "rough2.dot")
for i=0:2
    a = compile(altermu(2^i, 0, true, true))
    @show i, num_nodes(a)
end

for i=0:4
    a = compile(altermu(2^i, 0, false, false))
    @show i, num_nodes(a)
end

infer(f1, :bdd)
dump_dot(a, "rough3.dot")

for i = 0:10
    f = altermu(2^i, 1, false, false)
    a = compile(f)
    @show i, num_flips(a), num_nodes(a), infer(a)
end