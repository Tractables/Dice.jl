using Dice
using BenchmarkTools

function fun()

    c = @dice begin 
        n = 4

        id = Vector(undef, n)
        for i in 1:n
            id[i] = uniform(DistUInt{7}, 0, 10)
        end 

        id_obs = [2, 0, 5, 6]

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

        
        

        (id[1], id[2], id[3], id[4])
    end 
    debug_info_ref = Ref{CuddDebugInfo}()
    pr(c, ignore_errors=true, algo=Cudd(debug_info_ref=debug_info_ref))
    println("NUM_NODES_START")
    println(debug_info_ref[].num_nodes)
    println("NUM_NODES_END")
end 

x = @benchmark fun()
println((median(x).time)/10^9)