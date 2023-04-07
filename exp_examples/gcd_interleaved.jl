
using Dice 
using BenchmarkTools


localARGS = ARGS
# @show localARGS
i = parse(Int64, localARGS[1])
i = 3
# x = begin 
#     code = @dice begin  
    a_b = Vector(undef, i+1)
    b_b = Vector(undef, i+1) 
    code = @dice begin


        a_b[1] = false
        b_b[1] = false

        for j=2:i+1
            a_b[j]=flip(0.5)
            b_b[j]=flip(0.5)
        end

    

        a = DistUInt(a_b) + DistUInt{i+1}(1)
        b = DistUInt(b_b) + DistUInt{i+1}(1)
        for _ = 1 : 1 + (i+1) ÷ log2(MathConstants.golden)
            t = b
            converged = prob_equals(b, DistUInt{i+1}(0))
            amb = a % b
            b = ifelse(converged, b, amb)
            a = ifelse(converged, a, t)
        end
        gcd=a
        # prob_equals(g, DistUInt{i+1}(1))
        gcd
        # DistUInt(a_b)
    end
#     end

    pr(code, ignore_errors=true)
# end

# println(i, " ", (median(x).time)/10^9)
# @show (median(x).time)/(10^9)

# @show @benchmark pr(c)