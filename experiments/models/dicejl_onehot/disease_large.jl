using Dice 
using BenchmarkTools

function fun() 
    c = @dice begin 
        function binomial(n::DistUInt{W}, p, max::Int) where W 
            output = DistUInt{W}(0)
            for i in 0:max-1 
                output += ifelse((DistUInt{W}(i)<n) & flip(p), DistUInt{W}(1), DistUInt{W}(0))
            end 
            return output 
        end 
        

        param = uniform(DistUInt{12}, 500, 1501)
        nummet = binomial(param, 0.5, 1500)
        numinfected = binomial(nummet, 0.3, 1500)
        numinfected
    end

    pr(c)
end 

x = @benchmark fun()

println((median(x).time)/10^9)