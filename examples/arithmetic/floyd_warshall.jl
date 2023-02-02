using Dice 




c = @dice begin 
    num_nodes = 6
    MAX = 3 * num_nodes * num_nodes
    w = Int(floor(log2(MAX))) + 2

    edges = Dict(
        (1, 2) => uniform(DistUInt{w}, 1, 3),
        (1, 3) => uniform(DistUInt{w}, 1, 5),
        (1, 6) => uniform(DistUInt{w}, 1, 11),
        (2, 3) => uniform(DistUInt{w}, 1, 3),
        (2, 5) => uniform(DistUInt{w}, 1, 7),
        (3, 5) => uniform(DistUInt{w}, 1, 5),
        (4, 5) => uniform(DistUInt{w}, 1, 3),
        (5, 6) => uniform(DistUInt{w}, 1, 3)
    ) 

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

    distance[1][6]
end

x = pr(c)

@show sort(collect(x), by=x->x[2], rev=true)
