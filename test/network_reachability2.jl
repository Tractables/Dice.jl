using Pkg; Pkg.activate(@__DIR__);

using Dice: @dice, num_flips, num_nodes

# TODO fix @dice macro to allow moving `reachable` outside of the macro code block

@dice begin

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

    n = 9

    # run on sampled deterministic graph
    adjacency_sampled = rand(Bool,n,n)
    reachable(adjacency_sampled, 1, n)

    # run on random graph
    adjacency_rand = [flip(0.5) for i=1:n, j=1:n]
    r = reachable(adjacency_rand, 1, n)

    @assert num_flips(r) == n*n-3n+3
    println("Number of flips used: $(num_flips(r))")
    println("Number of BDD nodes: $(num_nodes(r))")

end

