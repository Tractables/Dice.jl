using Dice
using Dice: num_flips, num_nodes, to_dice_ir

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
r = reachable(adjacency_sampled, 1, n)
println("Sampled graph reachability: ", r)

# run on random graph
code = @dice_ite begin
    adjacency_rand = [flip(0.5) for i=1:n, j=1:n]
    reachable(adjacency_rand, 1, n)
end

# BDD analysis
bdd = compile(code)
num_flips(bdd), num_nodes(bdd)
@assert num_flips(bdd) == n*n-3n+3
infer(code, :bdd)

# IR analysis
to_dice_ir(code)

# # TODO fix loopy let identifiers
# has_dice_binary() && rundice(code)
# has_dice_binary() && infer(code, :ocaml)
