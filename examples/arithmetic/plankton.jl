using Dice 


c = @dice begin 
    function binomial(n::DistUInt{W}, p::Float, max::Int) where W 
        output = DistUInt{W}(0)
        for i in 0:max-1 
            output += ifelse(DistUInt{W}(i)<n & flip(p), DistUInt{W}(1), DistUInt{W}(0))
        end 
        return output 
    end 
end
    
    


