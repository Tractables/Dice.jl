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
        

        param = uniform(DistUInt{12}, 50, 101)
        nummet = binomial(param, 0.5, 100)
        numinfected = binomial(nummet, 0.3, 100)
        numinfected
    end

    debug_info_ref = Ref{CuddDebugInfo}()
    pr(c, algo=Cudd(debug_info_ref=debug_info_ref))
    println("NUM_NODES_START")
    println(debug_info_ref[].num_nodes)
    println("NUM_NODES_END")
end 

fun()