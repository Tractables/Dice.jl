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

n = 7

# run on sampled deterministic graph
adjacency_sampled = rand(Bool, n, n)
r = reachable(adjacency_sampled, 1, n)
println("Sampled graph reachability: ", r)

# run on random graph
code = @dice begin
    adjacency_rand = [flip(0.5) for i=1:n, j=1:n]
    reachable(adjacency_rand, 1, n)
end

# BDD analysis
bdd = compile(code)
println("Number of flips used: $(num_flips(bdd))")
println("Number of BDD nodes: $(num_nodes(bdd))")
@assert num_flips(bdd) == n*n-3n+3

# IR analysis
# TODO: add let expressions to the IR
# println(to_dice_ir(code))
# has_dice_binary() && rundice(code)
# has_dice_binary() && infer(code, :ocaml)

