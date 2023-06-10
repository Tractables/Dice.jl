using Dice 
using BenchmarkTools

function fun() 
    c = @dice begin 
        function binomial(n::DistUIntOH{W}, p, max::Int) where W 
            output = DistUIntOH{W}(0)
            for i in 0:max-1 
                output += ifelse((DistUIntOH{W}(i)<n) & flip(p), DistUIntOH{W}(1), DistUIntOH{W}(0))
            end 
            return output 
        end 
        

        param = uniform(DistUIntOH{102}, 50, 101)
        nummet = binomial(param, 0.5, 100)
        numinfected = binomial(nummet, 0.3, 100)
        numinfected
    end

    pr(c)
end 

x = @benchmark fun()

println((median(x).time)/10^9)