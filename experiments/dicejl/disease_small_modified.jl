using Dice 

function binomial(n::DistUInt{W}, p, max::Int) where W 
    output = DistUInt{W}(0)
    for i in max-1:-1:0 
        output += ifelse((DistUInt{W}(i) < n) & flip(p), 
            DistUInt{W}(1), DistUInt{W}(0))
    end 
    return output 
end 

@time begin
    DInt = DistUInt{7}
    param = uniform(DInt, 0, 51) + DInt(50)
    nummet = binomial(param, 0.5, 100) + DInt(1)
    numinfected = binomial(nummet, 0.3, 101)
    pr(numinfected)
end
