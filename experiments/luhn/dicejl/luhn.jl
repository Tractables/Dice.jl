using Dice
using BenchmarkTools



function fun()
    n = if length(ARGS) == 1 parse(Int64, ARGS[1]) else 5 end
    
    id_obs = [2, 0, 5, 6, 0, 6, 7, 1, 7, 8]
    c = @dice begin 

        id = Vector(undef, n)
        for i in 1:n
            id[i] = uniform(DistUInt{7}, 0, 10)
        end 

        for i in 1:n
            observe(ifelse(flip(1/2), prob_equals(id[i], DistUInt{7}(id_obs[i])), true))
        end 


        sum = DistUInt{7}(0)
        for i in 2:n
            if i % 2 == 0
                sum = sum + id[i]
            else 
                sum = sum +  ifelse(id[i] > DistUInt{7}(4), DistUInt{7}(2) * id[i] - DistUInt{7}(9), DistUInt{7}(2) * id[i])
            end 
        end 

        mod = sum % DistUInt{7}(10)

        observe(prob_equals(id[1], DistUInt{7}(10)-mod))

        
        

        id[1]
    end 
    pr(c, ignore_errors=true)
end 

x = @benchmark fun()
println((median(x).time)/10^9)