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
        

        param = uniform(DistUInt{7}, 10, 51)
        planktoncount = binomial(param, 0.5, 50)
        planktoncount
    end

    debug_info_ref = Ref{CuddDebugInfo}()
    pr(c, algo=Cudd(debug_info_ref=debug_info_ref))
    println("NUM_NODES_START")
    println(debug_info_ref[].num_nodes)
    println("NUM_NODES_END")
end 
fun()