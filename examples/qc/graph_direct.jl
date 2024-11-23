using Dice
import Base: all, any

all(itr) = reduce(&, itr)

function Dice.prob_equals(graph1::Matrix, graph2::Matrix)
    size(graph1) == size(graph2) && all(prob_equals(graph1[i,j], graph2[i,j]) for i in 1:NUM_NODES for j in 1:NUM_NODES)
end

DU8 = DistUInt{8}
DU8_Inf = DistUInt{8}([true for _ in 1:8])

function find_longest_distance(graph::Matrix)
    # Convert boolean adjacency matrix to distance matrix
    # true -> 1 (connected), false -> Inf (not connected)
    n = size(graph)[1]
    dist = Array{DU8}(undef, n, n)
    for i in 1:n, j in 1:n
        if i == j
            dist[i,j] = DU8(0)
        else
            dist[i,j] = @dice_ite if graph[i,j] DU8(1) else DU8_Inf end
        end
    end

    # last_print = nothing
    # function maybe_print(meta)
    #     x = map(dist) do x Dice.frombits(x, Dict()) end
    #     if x != last_print
    #         @show meta
    #         display(x)
    #         last_print = x
    #     end
    # end
    # maybe_print(nothing)
    
    # Floyd-Warshall algorithm to find shortest paths between all pairs
    # last_print = 

    for k in 1:n
        for i in 1:n
            for j in 1:n
                dist[i,j] = @dice_ite if prob_equals(dist[i,k], DU8_Inf) | prob_equals(dist[k,j], DU8_Inf)
                    dist[i,j]
                else
                    min(dist[i,j], dist[i,k] + dist[k,j])
                end
                # maybe_print((k,i,j,
                #     "i-k: $(Dice.frombits(dist[i,k],Dict()))  "*
                #     "k-j: $(Dice.frombits(dist[k,j],Dict()))  "*
                #     "i-k-j: $(Dice.frombits(dist[i,k]+dist[k,j],Dict()))  "
                # ))
            end
        end
    end
    
    # Find the maximum finite distance
    max_dist = DU8(0)
    for i in 1:n
        for j in 1:n
            max_dist = @dice_ite if (!prob_equals(dist[i,j], DU8_Inf)) & (dist[i,j] > max_dist)
                dist[i,j]
            else
                max_dist
            end
        end
    end
    max_dist
    # dist
end

using Test

# Helper function to create adjacency matrix from edge list
function create_graph(n::Int, edges::Vector{Tuple{Int,Int}})
    graph = zeros(Bool, n, n)
    for (from, to) in edges
        graph[from, to] = true
    end
    return graph
end

function test()
@testset "find_longest_distance" begin
    # Test 1: Simple path
    @test begin
        graph = create_graph(3, [(1,2), (2,3)])
        Dice.frombits(find_longest_distance(graph), Dict()) == 2
    end

    # Test 2: Cycle
    @test begin
        graph = create_graph(4, [(1,2), (2,3), (3,4), (4,1)])
        Dice.frombits(find_longest_distance(graph), Dict()) == 3
    end

    # Test 3: Disconnected graph
    @test begin
        graph = create_graph(4, [(1,2), (3,4)])
        Dice.frombits(find_longest_distance(graph), Dict()) == 1
    end

    # Test 6: Complex graph with multiple paths
    @test begin
        graph = create_graph(6, [
            (1,2), (2,3), (3,4), (4,5), (5,6),  # Long path
            (1,3), (3,5), (2,4), (4,6)          # Shortcuts
        ])
        Dice.frombits(find_longest_distance(graph), Dict()) == 3
    end

    @test begin
        graph = create_graph(6, [
            (1,2), (2,3), (3,4), (4,5), (5,6),  # Long path
        ])
        Dice.frombits(find_longest_distance(graph), Dict()) == 5
    end


    # Test 7: Graph with self-loops
    @test begin
        graph = create_graph(3, [(1,1), (1,2), (2,3)])
        Dice.frombits(find_longest_distance(graph), Dict()) == 2
    end

    # Test 8: Complete graph
    @test begin
        n = 4
        graph = ones(Bool, n, n)
        Dice.frombits(find_longest_distance(graph), Dict()) == 1
    end

    # Test error cases
    @test_throws ArgumentError find_longest_distance([true true; true])  # Non-square matrix
    
    # Test 9: Graph with bidirectional edges
    @test begin
        graph = create_graph(4, [(1,2), (2,1), (2,3), (3,2), (3,4), (4,3)])
        Dice.frombits(find_longest_distance(graph), Dict()) == 3
    end
end
end
test()

function generate_graph(n, directed, var_vals)
    graph = Matrix{Dice.AnyBool}(undef, n, n)
    for from in 1:n
        for to in 1:n
            graph[from, to] = if from > to && directed
                graph[to, from]
            else
                v = Var((from, to))
                var_vals[v] = 0
                flip(sigmoid(v))
            end
        end
    end
    graph
end


NUM_NODES = 10 # 42
TARGET
DIRECTED = false
var_vals = Valuation()
g = generate_graph(NUM_NODES, DIRECTED, var_vals)

a = ADComputer(var_vals)

dist = find_longest_distance(g)
l = Dice.LogPrExpander(WMC(BDDCompiler(Dice.tobits(dist))))

loss = -LogPr(prob_equals(dist, DU8(8)))
loss_expanded = Dice.expand_logprs(l, loss)

vals, derivs = differentiate(
    var_vals,
    Derivs(loss => 1)
)
for (adnode, d) in derivs
    if adnode isa Var
        var_vals[adnode] -= d * LR
    end
end

# [derivs[var] for var in var_vals if var in derivs]

# s = samples[1]
# prob_equals(g, s)
# compute_mixed(var_vals, LogPr(prob_equals(g, sample(a,g))))

# println(var_vals)

# a = ADComputer(var_vals)
# for attempt in 1:1000
#     sample()