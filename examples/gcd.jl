using Dice 

code = @dice begin 
    function gcd(a::DistUInt{W}, b::DistUInt{W}) where W
        for _ = 1 : 1 + W ÷ log2(MathConstants.golden)
            amb = a % b
            amb = ifelse(prob_equals(amb, DistUInt{W}(0)), b, amb)
            b, a = amb, b
        end
        return a
    end

    n = 4
    a = uniform(DistUInt16, n) + DistUInt16(1)
    b = uniform(DistUInt16, n) + DistUInt16(1)
    g = gcd(a, b)
    prob_equals(g, DistUInt16(1))
end 

pr(code)