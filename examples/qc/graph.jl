using Dice
import Base: all, any

all(itr) = reduce(&, itr)

function Dice.prob_equals(graph1::Matrix, graph2::Matrix)
    size(graph1) == size(graph2) && all(prob_equals(graph1[i,j], graph2[i,j]) for i in 1:NUM_NODES for j in 1:NUM_NODES)
end

function find_longest_distance(graph::Matrix{Bool})
    # Input validation
    n = size(graph, 1)
    if !isquadratic(graph)
        throw(DimensionMismatch("Input matrix must be square"))
    end
    
    # Handle empty or single-node graphs
    if n ≤ 1
        return 0
    end
    
    # Convert boolean adjacency matrix to distance matrix
    # true -> 1 (connected), false -> Inf (not connected)
    dist = Array{Float64}(undef, n, n)
    for i in 1:n, j in 1:n
        if i == j
            dist[i,j] = 0
        else
            dist[i,j] = graph[i,j] ? 1.0 : Inf
        end
    end
    
    # Floyd-Warshall algorithm to find shortest paths between all pairs
    for k in 1:n
        for i in 1:n
            for j in 1:n
                if dist[i,k] != Inf && dist[k,j] != Inf
                    dist[i,j] = min(dist[i,j], dist[i,k] + dist[k,j])
                end
            end
        end
    end
    
    # Find the maximum finite distance
    max_dist = 0
    for i in 1:n
        for j in 1:n
            if dist[i,j] != Inf && dist[i,j] > max_dist
                max_dist = dist[i,j]
            end
        end
    end
    
    return Int(max_dist)
end

# Helper function to check if matrix is square
function isquadratic(matrix::Matrix)
    size(matrix, 1) == size(matrix, 2)
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
        find_longest_distance(graph) == 2
    end

    # Test 2: Cycle
    @test begin
        graph = create_graph(4, [(1,2), (2,3), (3,4), (4,1)])
        find_longest_distance(graph) == 3
    end

    # Test 3: Disconnected graph
    @test begin
        graph = create_graph(4, [(1,2), (3,4)])
        find_longest_distance(graph) == 1
    end

    # Test 4: Single node
    @test begin
        graph = zeros(Bool, 1, 1)
        find_longest_distance(graph) == 0
    end

    # Test 5: Empty graph
    @test begin
        graph = zeros(Bool, 0, 0)
        find_longest_distance(graph) == 0
    end

    # Test 6: Complex graph with multiple paths
    @test begin
        graph = create_graph(6, [
            (1,2), (2,3), (3,4), (4,5), (5,6),  # Long path
            (1,3), (3,5), (2,4), (4,6)          # Shortcuts
        ])
        find_longest_distance(graph) == 3
    end

    @test begin
        graph = create_graph(6, [
            (1,2), (2,3), (3,4), (4,5), (5,6),  # Long path
        ])
        find_longest_distance(graph) == 5
    end


    # Test 7: Graph with self-loops
    @test begin
        graph = create_graph(3, [(1,1), (1,2), (2,3)])
        find_longest_distance(graph) == 2
    end

    # Test 8: Complete graph
    @test begin
        n = 4
        graph = ones(Bool, n, n)
        find_longest_distance(graph) == 1
    end

    # Test error cases
    @test_throws ArgumentError find_longest_distance([true true; true])  # Non-square matrix
    
    # Test 9: Graph with bidirectional edges
    @test begin
        graph = create_graph(4, [(1,2), (2,1), (2,3), (3,2), (3,4), (4,3)])
        find_longest_distance(graph) == 3
    end
end
end


NUM_NODES = 20 # 42
DIRECTED = false

function generate_graph(n, directed, var_vals)
    graph = Matrix{Dice.AnyBool}(undef, n, n)
    for from in 1:n
        for to in 1:n
            graph[from, to] = if from > to && directed
                graph[to, from]
            else
                v = Var((from, to))
                var_vals[v] = inverse_sigmoid(0.1)
                flip(sigmoid(v))
            end
        end
    end
    graph
end

function sample(a::ADComputer, graph::Matrix{Dice.AnyBool})
    map(graph) do f rand() < compute(a, f.prob) end
end

var_vals = Valuation()
g = generate_graph(NUM_NODES, DIRECTED, var_vals)
NUM_EPOCHS = 100
NUM_SAMPLES = 1000
LR = 0.03
@time for epoch in 1:NUM_EPOCHS
    a = ADComputer(var_vals)
    samples = [sample(a, g) for _ in 1:NUM_SAMPLES ]

    l = Dice.LogPrExpander(WMC(BDDCompiler([
        prob_equals(g,sample)
        for sample in samples
    ])))
    loss, total_dist = sum(
        begin
            lpr_eq = Dice.expand_logprs(l, LogPr(prob_equals(g, sample)))
            dist = find_longest_distance(sample)
            [-lpr_eq * dist, dist]
        end
        for sample in samples
    )
    println(total_dist / length(samples))

    vals, derivs = differentiate(
        var_vals,
        Derivs(loss => 1)
    )
    for (adnode, d) in derivs
        if adnode isa Var
            var_vals[adnode] -= d * LR
        end
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