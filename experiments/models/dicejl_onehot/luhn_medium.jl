using Dice
using BenchmarkTools

function fun()

    c = @dice begin 
        n = 6

        id = Vector(undef, n)
        for i in 1:n
            id[i] = uniform(DistUIntOH{60}, 0, 10)
        end 

        id_obs = [2, 0, 5, 6, 0, 0]

        for i in 1:n
            observe(ifelse(flip(1/2), prob_equals(id[i], DistUIntOH{60}(id_obs[i])), true))
        end 


        sum = DistUIntOH{60}(0)
        for i in 2:n
            if i % 2 == 0
                sum = sum + id[i]
            else 
                sum = sum +  ifelse(id[i] > DistUIntOH{60}(4), DistUIntOH{60}(2) * id[i] - DistUIntOH{60}(9), DistUIntOH{60}(2) * id[i])
            end 
        end 

        mod = sum % DistUIntOH{60}(10)

        observe(prob_equals(id[1], DistUIntOH{60}(10)-mod))

        
        

        (id[1], id[2], id[3], id[4], id[5], id[6])
    end 
    pr(c, ignore_errors=true)
end 

x = @benchmark fun()
println((median(x).time)/10^9)