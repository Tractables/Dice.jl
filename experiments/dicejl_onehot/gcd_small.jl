using Dice 
using BenchmarkTools


function fun() 
    c = @dice begin 
        function gcd(a::DistUIntOH{W}, b::DistUIntOH{W}) where W
            for _ = 1 : 1 + W ÷ log2(MathConstants.golden)
                amb = a % b
                amb = ifelse(prob_equals(amb, DistUIntOH{W}(0)), b, amb)
                b, a = amb, b
            end
            return a
        end

        a = uniform(DistUIntOH{257}, 1, 257)
        b = uniform(DistUIntOH{257}, 1, 257)
        prob_equals(gcd(a, b), DistUIntOH{257}(1))
    end 
    pr(c)
end 
fun()
# x = @benchmark fun() 

println((median(x).time)/10^9)
