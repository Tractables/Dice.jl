using Dice

vend_model = @dice begin 
    coin1 = if flip(0.5) DistUInt8(10) else DistUInt8(25) end 
    coin2 = if flip(0.5) DistUInt8(10) else DistUInt8(25) end 

    s1 = if flip(0.8) coin1 else DistUInt8(0) end 
    s2 = if flip(0.8) coin2 + s1 else s1 end 

    candy = (s2 >= DistUInt8(15))
    observe(candy)
    coin1 
end 

pr(vend_model)