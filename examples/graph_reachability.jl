using Dice

function reachable(adjacency::Matrix, src::Int, dest::Int)
    n = size(adjacency, 1)
    reachable = Vector(undef, n)
    reachable .= false
    reachable[src] = true
    for i=1:n
        for node=1:n
            reachable[node] |= reduce(|, reachable .& adjacency[:, node])
        end
    end
    reachable[dest]
end

n = 5

# run on sampled deterministic graph
adjacency_sampled = rand(Bool, n, n)
x = reachable(adjacency_sampled, 1, n)
println("Sampled graph reachability: ", x)

# run on random graph
adjacency_rand = [flip(0.5) for i=1:n, j=1:n]
y = reachable(adjacency_rand, 1, n)
println("Random graph reachability: ", pr(y)[true])
