using Dice
using BenchmarkTools

function fun()
    c = @dice begin 
        char_freqs = [0.082, 0.018, 0.024, 0.04, 0.123, 0.022, 0.022, 0.066, 0.069, 0.001, 0.008, 0.045, 0.024, 0.069, 0.073, 0.018, 0.002, 0.055, 0.067, 0.092, 0.028, 0.009, 0.023, 0.001, 0.018, 0.001]
        key = uniform(DistUInt{7}, 0, 26)
        
        function sendChar(key::DistUInt{7}, c::DistUInt{7})
            gen = discrete(DistUInt{7}, char_freqs)
            enc = key + gen 
            enc = ifelse(enc > DistUInt{7}(25), enc-DistUInt{7}(26), enc)
            observe(prob_equals(enc, c))
        end 

        text = [9, 11, 8, 21, 20, 21, 2, 5, 2, 12]
        for char in text
            sendChar(key, DistUInt{7}(char))
        end 
        key 
    end  

    debug_info_ref = Ref{CuddDebugInfo}()
    pr(c, ignore_errors=true, algo=Cudd(debug_info_ref=debug_info_ref))
    println("NUM_NODES_START")
    println(debug_info_ref[].num_nodes)
    println("NUM_NODES_END") 
end 

fun()

