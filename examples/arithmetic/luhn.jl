using Dice

c = @dice begin 
    n = 6

    id = Vector(undef, n)
    for i in 1:n
        id[i] = uniform(DistUInt{7}, 0, 10)
    end 

    id_obs = [5, 0, 5, 6, 1, 0]

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

    
    

    (id[1], id[2], id[3], id[4], id[5], id[6])
end 

x = pr(c, ignore_errors=true)
sort(collect(x), by=x->x[2], rev=true)
x[(5, 0, 5, 1, 6)]