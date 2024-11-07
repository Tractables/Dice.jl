using Dice 

function binomial(n::DistUIntOH{W}, p, max::Int) where W 
    output = DistUIntOH{W}(0)
    for i in max-1:-1:0 
        output += ifelse((DistUIntOH{W}(i) < n) & flip(p), 
            DistUIntOH{W}(1), DistUIntOH{W}(0))
    end 
    return output 
end 

@time begin
    DInt = DistUIntOH{102}
    param = uniform(DInt, 0, 51) + DInt(50)
    nummet = binomial(param, 0.5, 100) + DInt(1)
    numinfected = binomial(nummet, 0.3, 101)
    pr(numinfected)
end
