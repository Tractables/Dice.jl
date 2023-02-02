using Dice 

c = @dice begin
    # a = uniform(DistInt{22},-1000, 1000)
    # b = uniform(DistInt{22},-1000, 1000)
    # c = uniform(DistInt{22},-1000, 1000)
    a = uniform(DistInt{15},-100, 101)
    b = uniform(DistInt{15},-100, 101)
    c = uniform(DistInt{15},-100, 101)



    zero = DistInt{15}(0)


    type = 
        ifelse((a <= zero) | (b <= zero) | (c <= zero), 
            DistUInt{2}(3),
        ifelse(
            (a+b<=c) | (a+c<=b) | (b+c <= a), 
            DistUInt{2}(3),
        ifelse(
            prob_equals(a, b) & prob_equals(a, c) & prob_equals(b, c),
            DistUInt{2}(2), 
        ifelse(
            prob_equals(a, b) | prob_equals(a, c) | prob_equals(b, c), 
            DistUInt{2}(1), 
            DistUInt{2}(0)
        ))))

    type 

end

@show pr(c)
