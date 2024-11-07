using Dice
using BenchmarkTools

function fun() 
    c = @dice begin 
        uniq_count = 4
        bits = Int(floor(log2(uniq_count)) + 4)

        rankings = [[3, 2, 1, 0], 
                    [1, 3, 2, 0],
                    [1, 2, 3, 0], 
                    [3, 1, 2, 0],
                    [3, 2, 1, 0]]

        ranks = [uniform(DistIntOH{-4, 13}, 0, uniq_count) for i in 1:uniq_count]
        for i in 1:uniq_count
            for j in i+1:uniq_count
                observe(!prob_equals(ranks[i], ranks[j]))
            end
        end
        

        for data in rankings 
            obs_rank = [x + uniform(DistIntOH{-4, 13}, -uniq_count, uniq_count+1) for x in ranks]
            for i in 1:uniq_count-1
                a, b = data[i]+1, data[i+1] + 1
                observe(obs_rank[a] < obs_rank[b])
            end 
        end 

        (ranks[1], ranks[2], ranks[3], ranks[4])
    end
    pr(c)
end 

x = @benchmark fun()

println((median(x).time)/10^9)