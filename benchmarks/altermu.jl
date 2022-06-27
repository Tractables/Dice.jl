using Revise
using Dice
using Dice: num_flips, num_nodes, to_dice_ir
using Distributions
using StatsBase
using Distances

function altermu(p::Int, binbits::Int)
    
    code = @dice begin
        #The final type of the output
        # binbits = binbit+2
        t = DistSigned{binbits + 5, binbits} 

        # The Gaussian in range [-2, 2] with two additional precision
        mu1 = add_bits(continuous(dicecontext(), p, DistSigned{binbits + 4, binbits + 2}, Normal(0, 5)), 3, 0)
        mu2 = add_bits(continuous(dicecontext(), p, DistSigned{binbits + 4, binbits + 2}, Normal(0, 5)), 3, 0)

        a = DistSigned{2*binbits + 8, 2*binbits + 4}((add_bits(mu1, 4 + binbits, 0) * add_bits(mu2, 4 + binbits, 0))[1])
        a = t(a.number.bits[binbits + 5:2*binbits + 9])

        mu3 = add_bits(continuous(dicecontext(), p, DistSigned{binbits + 2, binbits}, Normal(0, 5)), 3, 0)

        mean = (a - mu3)[1]
        
        data = [-2.57251482,  0.33806206,  2.71757796,  1.09861336,  2.85603752,
        -0.91651351,  0.15555127, -2.68160347,  2.47043789,  3.47459025,
        1.63949862, -1.32148757,  2.64187513,  0.30357848, -4.09546231,
        -1.50709863, -0.99517866, -2.0648892 , -2.40317949,  3.46383544,
        0.91173696,  1.18222221,  0.04235722, -0.52815171,  1.15551598,
        -1.62749724,  0.71473237, -1.08458812,  4.66020296,  1.24563831,
        -0.67970862,  0.93461681,  1.18187607, -1.49501051,  2.44755622,
        -2.06424237, -0.04584074,  1.93396696,  1.07685273, -0.09837907]
        
        obs = true
        for i = 1:length(data)
            y1 = (mean + continuous(dicecontext(), p, t, Normal(0, 1)))[1]
            obs &= prob_equals(y1, t(dicecontext(), data[i]))
        end
        Cond(mu1, obs)
        mu1
    end
    code
end

infer(altermu(2, 1), :bdd)
localARGS = ARGS
@show localARGS
j = parse(Int64, localARGS[2])
i = parse(Int64, localARGS[1])

@show j, i
code = altermu(2^j, i)
d = @timed expectation(code, :bdd)
b = d.value[2]
c = d.value[3]
# @show d, b, c
e = @timed variance(code, :bdd)
io = open("/space/poorvagarg/.julia/dev/Dice/altermu_mu1_results.txt", "a")
@show i, j, b, c, d.time, d.value[1], e.time, e.value
writedlm(io, [i j b c d.time d.value[1] e.time e.value], ",")  
close(io)