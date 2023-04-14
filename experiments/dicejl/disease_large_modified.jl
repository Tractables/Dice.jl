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
    DInt = DistUInt{12}
    param = uniform(DInt, 0, 1001) + DInt(500)
    nummet = binomial(param, 0.5, 1500) + DInt(1)
    numinfected = binomial(nummet, 0.3, 1501)
    pr(numinfected)
end
