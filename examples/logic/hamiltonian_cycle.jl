using Dice

# (1)--(2)--(3)
#  |   / \   |
#  |  /   \  |
#  | /     \ |
# (4)-------(5)
NUM_NODES = 5
EDGES = [(1, 2), (2, 3), (3, 5), (5, 4), (4, 1), (2, 4), (2, 5)]

md = @dice begin
    # Choose path
    path = [
        uniform(DistUInt32, 1, NUM_NODES + 1)
        for _ in 1:NUM_NODES
    ]
    
    # Dist-version of EDGES
    edges = DistVector([DistVector([DistUInt32(u), DistUInt32(v)]) for (u, v) in EDGES])

    # every node visited
    for node in map(DistUInt32, 1:NUM_NODES)
        observe(prob_contains(DistVector(path), node))
    end

    # edges exist along path
    for (i, node) in enumerate(path)
        next_node = if i == length(path) path[1] else path[i + 1] end
        observe(
            prob_contains(edges, DistVector([node, next_node]))
            | prob_contains(edges, DistVector([next_node, node]))
        )
    end

    # assume we start at node 1 (don't distinguish "rotations" of the same path)
    observe(prob_equals(path[1], DistUInt32(1)))

    path
end

pr(md)
