using Alea

NUM_NODES = 4
NUM_COLORS = 3
EDGES = [(1, 2), (2, 3), (3, 1), (1, 4)]

md = @dice begin
    node_colors = [
        uniform(DistUInt32, 0, NUM_COLORS)
        for _ in 1:NUM_NODES
    ]

    for (u, v) in EDGES
        observe(!prob_equals(node_colors[u], node_colors[v]))
    end
    node_colors
end

pr(md)
