using Dice
using BenchmarkTools

function fun() 


    c = @dice begin
    players = Vector(undef, 6)

    players[1] = discrete(DistUIntOH{500}, [0.015625, 0.09375, 0.234375, 0.3125, 0.234375, 0.09375, 0.015625]) + DistUIntOH{500}(142);
    players[2] = discrete(DistUIntOH{500}, [0.015625, 0.09375, 0.234375, 0.3125, 0.234375, 0.09375, 0.015625]) + DistUIntOH{500}(146);
    players[3] = discrete(DistUIntOH{500}, [0.015625, 0.09375, 0.234375, 0.3125, 0.234375, 0.09375, 0.015625]) + DistUIntOH{500}(150);
    players[4] = discrete(DistUIntOH{500}, [0.015625, 0.09375, 0.234375, 0.3125, 0.234375, 0.09375, 0.015625]) + DistUIntOH{500}(143);
    players[5] = discrete(DistUIntOH{500}, [0.015625, 0.09375, 0.234375, 0.3125, 0.234375, 0.09375, 0.015625]) + DistUIntOH{500}(145);
    players[6] = discrete(DistUIntOH{500}, [0.015625, 0.09375, 0.234375, 0.3125, 0.234375, 0.09375, 0.015625]) + DistUIntOH{500}(140);


    cheat_player = uniform(DistUInt{3}, 0, 6)
    cheat_player2 = uniform(DistUInt{3}, 0, 6)
    observe(!prob_equals(cheat_player, cheat_player2))

    final_players = Vector(undef, 6)
    for i in 1:6
        final_players[i] = ifelse(prob_equals(cheat_player, DistUInt{3}(i-1)) | prob_equals(cheat_player2, DistUInt{3}(i-1)), players[i]+DistUIntOH{500}(10), players[i])
    end

    a = final_players[1]
    b = final_players[2]
    c = final_players[3]
    d = final_players[4]
    e = final_players[5]
    f = final_players[6]

    
    result_3 = a+b+e<c+d+f 
    result_5 = a+c+d<b+e+f 
    result_6 = a+c+e<b+d+f
    result_10 = a+e+f<b+c+d

    observe(result_3 & result_5 & result_6 & result_10)
    (cheat_player == DistUInt{3}(5)) | (cheat_player2 == DistUInt{3}(5))
    end



    debug_info_ref = Ref{CuddDebugInfo}()
    pr(c, algo=Cudd(debug_info_ref=debug_info_ref))
    println("NUM_NODES_START")
    println(debug_info_ref[].num_nodes)
    println("NUM_NODES_END")
end
fun()