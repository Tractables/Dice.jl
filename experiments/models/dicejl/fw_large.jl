using Dice 
using BenchmarkTools


function fun()

    c = @dice begin 
        num_nodes = 8
        MAX = num_nodes * 3 * num_nodes
        w = Int(floor(log2(MAX))) + 2
        edge_list = [[0, 2],
        [0, 4],
        [0, 5],
        [0, 6],
        [1, 4],
        [1, 6],
        [2, 3],
        [2, 7],
        [3, 6],
        [3, 7],
        [4, 7],
        [5, 6],
        [6, 7]]
        edges = Dict() 

        for edge in edge_list
            diff = edge[2] - edge[1]
            half = Int(floor((diff/2)))
            edges[(edge[1]+1, edge[2]+1)] = uniform(DistUInt{w}, 1, 2*diff+1) 
        end 


        distance = [[DistUInt{w}(MAX) for j in 1:num_nodes] for i in 1:num_nodes]


        for edge in edges 
            coord, dist = edge[1], edge[2]
            distance[coord[1]][coord[2]] = dist  
            distance[coord[2]][coord[1]] = dist 
        end 

        for i in 1:num_nodes
            distance[i][i] = DistUInt{w}(0)
        end 


        for k in 1:num_nodes 
            for i in 1:num_nodes 
                for j in 1:num_nodes 
                    distance[i][j] = ifelse(distance[i][j] > distance[i][k]+distance[k][j], distance[i][k]+distance[k][j], distance[i][j])
                end 
            end 
        end     

        distance[1][8]
    end
    pr(c)
end 
x = @benchmark fun() 

println((median(x).time)/10^9)