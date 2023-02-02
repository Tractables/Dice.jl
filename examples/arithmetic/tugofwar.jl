using Dice



c = @dice begin
players = Vector(undef, 6)

players[1] = discrete(DistUInt{9}, [0.015625, 0.09375, 0.234375, 0.3125, 0.234375, 0.09375, 0.015625]) + DistUInt{9}(142);
players[2] = discrete(DistUInt{9}, [0.015625, 0.09375, 0.234375, 0.3125, 0.234375, 0.09375, 0.015625]) + DistUInt{9}(146);
players[3] = discrete(DistUInt{9}, [0.015625, 0.09375, 0.234375, 0.3125, 0.234375, 0.09375, 0.015625]) + DistUInt{9}(150);
players[4] = discrete(DistUInt{9}, [0.015625, 0.09375, 0.234375, 0.3125, 0.234375, 0.09375, 0.015625]) + DistUInt{9}(143);
players[5] = discrete(DistUInt{9}, [0.015625, 0.09375, 0.234375, 0.3125, 0.234375, 0.09375, 0.015625]) + DistUInt{9}(145);
players[6] = discrete(DistUInt{9}, [0.015625, 0.09375, 0.234375, 0.3125, 0.234375, 0.09375, 0.015625]) + DistUInt{9}(140);


cheat_player = uniform(DistUInt{3}, 0, 6)
cheat_player2 = uniform(DistUInt{3}, 0, 6)
observe(!prob_equals(cheat_player, cheat_player2))

final_players = Vector(undef, 6)
for i in 1:6
    final_players[i] = ifelse(prob_equals(cheat_player, DistUInt{3}(i-1)) | prob_equals(cheat_player2, DistUInt{3}(i-1)), players[i]+DistUInt{9}(10), players[i])
end

a = final_players[1]
b = final_players[2]
c = final_players[3]
d = final_players[4]
e = final_players[5]
f = final_players[6]

result_1 = a+b+c<d+e+f 
result_2 = a+b+d<c+e+f 
result_3 = a+b+e<c+d+f 
result_4 = a+b+f<c+d+e 
result_5 = a+c+d<b+e+f 
result_6 = a+c+e<b+d+f
result_7 = a+c+f<b+d+e
result_8 = a+d+e<b+c+f
result_9 = a+d+f<b+c+e
result_10 = a+e+f<b+c+d

observe(result_3 & result_5 & result_6 & result_10)
(cheat_player == DistUInt{3}(5)) | (cheat_player2 == DistUInt{3}(5))
end



@show pr(c)