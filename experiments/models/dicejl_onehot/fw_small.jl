using Dice 
using BenchmarkTools


function fun() 
    c = @dice begin 
        num_nodes = 3
        MAX = 14
        w = Int(floor(log2(MAX))) + 2

        edges = Dict(
            (1, 2) => uniform(DistUIntOH{15}, 1, 3),
            (1, 3) => uniform(DistUIntOH{15}, 3, 5),
            (2, 3) => uniform(DistUIntOH{15}, 2, 4)
        ) 

        distance = [[DistUIntOH{15}(MAX) for j in 1:num_nodes] for i in 1:num_nodes]


        for edge in edges 
            coord, dist = edge[1], edge[2]
            distance[coord[1]][coord[2]] = dist  
            distance[coord[2]][coord[1]] = dist 
        end 

        for i in 1:num_nodes
            distance[i][i] = DistUIntOH{15}(0)
        end 
        
        for k in 1:num_nodes 
            for i in 1:num_nodes 
                for j in 1:num_nodes 
                    distance[i][j] = ifelse(distance[i][j] > distance[i][k]+distance[k][j], distance[i][k]+distance[k][j], distance[i][j])
                end 
            end 
        end     

        distance[1][3]
    end

    pr(c)
end 

x = @benchmark fun()

println((median(x).time)/10^9)