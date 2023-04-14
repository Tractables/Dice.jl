using LinearAlgebra
using Dice 
using BenchmarkTools

function generate_graph(i)
    a = rand(1:i+1, (i, i))
    adj = tril(a) + transpose(tril(a,-1))
    return adj
end

function generate_lists(adjacency)
    n = size(adjacency)[1]
    # @show n 
    lists = Vector(undef, n)
    for i=1:n
        sublist = Vector(undef, n-1)
        for j=1:n
            if j < i
                sublist[j] = (j-1, adjacency[i,j])
            elseif j>i 
                sublist[j-1] = (j-1, adjacency[i,j])
            end
        end
        lists[i] = sublist
    end
    return lists
end

function program(nodes, steps, graph_lists)
    @dice begin 
    node_bits = Int(floor(log2(nodes))+1)
    cost_bits = Int(floor(log2((nodes+1)*steps))+1)
    # @show node_bits
    # @show cost_bits
    state = DistUInt{node_bits}(0)
    aggregate = DistUInt{cost_bits}(0)
    for i=1:steps
        node_list = 0:nodes-1
        node_check = [prob_equals(state, DistUInt{node_bits}(n)) for n=node_list]
        probs = [flip(1/i) for i=(nodes-1):-1:1]
        # @show probs
        function generate_ite(bits, list)
            # @show list
            ite_result_list = map(x->DistUInt{bits}(x), list)
            # @show ite_result_list
            # @show probs
            etc = collect(zip(probs, ite_result_list))
            # @show etc
            len = length(etc)
            return foldr(((x, y), z) -> ifelse(x, y, z), etc[1:len-1], init=etc[len][2])
        end
        
        graph_lists_node = map(x -> map(y->y[1], x), graph_lists)
        # @show graph_lists_node
        graph_lists_cost = map(x -> map(y->y[2], x), graph_lists)
        
        node_info = collect(zip(node_check, map(x->generate_ite(node_bits, x), graph_lists_node)))
        cost_info = collect(zip(node_check, map(x->generate_ite(cost_bits, x), graph_lists_cost)))
        # @show node_info
        # @show cost_info
        len = length(node_info)
        state_prob = foldr(((x, y), z) -> ifelse(x, y, z), node_info[1:len-1], init=node_info[len][2])
        cost_prob = foldr(((x, y), z) -> ifelse(x, y, z), cost_info[1:len-1], init=cost_info[len][2])
        # etc = zip(node_list, map(generate_ite, graph_lists))
        state = state_prob 
        aggregate = aggregate + cost_prob 
    end 
    goal=Int((nodes/3)*steps)
    return pr(aggregate>DistUInt{cost_bits}(goal))
end
end
localARGS = ARGS
# @show localARGS
num_nodes = parse(Int64, localARGS[1])
num_steps = parse(Int64, localARGS[2])
num_nodes = 3
num_steps = 3
graph = generate_graph(num_nodes)
graph_lists = generate_lists(graph)
# @show graph
# test =program(num_nodes, num_steps, graph_lists) 
# @show test
x = @benchmark program(num_nodes, num_steps, graph_lists) 
println(num_nodes, " ", num_steps, " ", (median(test).time)/10^9)
# n=3
# z = [1/i for i=(n-1):-1:1]
# @show z
# a=zip(y[1], z)
# @show a
# x= @dice begin 
#     node_bits = Int(floor(log2(3))+1)
#     @show node_bits
#     state = DistUInt{node_bits}(0)
# end