using Bijections
using LightGraphs
using TikzGraphs
using Metis

############################################ 
# graph representing dependencies between identifiers 
############################################
mutable struct IdDepGraph
    num_ids::Int
    id2int::Bijection{Identifier,Int}
    edges::Vector{Tuple{Int,Int}}
    id2expr::Dict{Identifier,DiceExpr}
end

function IdDepGraph()
    id2int = Bijection{Identifier,Int}()
    edges = Vector{Tuple{Int,Int}}()
    id2expr = Dict{Identifier,DiceExpr}()
    IdDepGraph(0, id2int, edges, id2expr)
end

function add_identifier!(g::IdDepGraph, id::Identifier, e::DiceExpr)
    next_int = (g.num_ids += 1)
    g.id2int[id] = next_int
    g.id2expr[id] = e
end

function add_dep!(g::IdDepGraph, parent::Identifier, child::Identifier)
    e = (g.id2int[parent], g.id2int[child])
    push!(g.edges, e)
end

############################################ 
# get dependency graph from Dice code 
############################################

function id_dep_graph(p::DiceProgram)::IdDepGraph
    g = IdDepGraph()
    id_dep_graph(p.expr, g, nothing)
    g
end

function id_dep_graph(e::LetExpr, g, child)
    add_identifier!(g, e.identifier, e.e1)
    if !isnothing(child)
        add_dep!(g, e.identifier, child)
    end
    id_dep_graph(e.e1, g, e.identifier)
    id_dep_graph(e.e2, g, child)
end

function id_dep_graph(e::Ite, g, child)
    id_dep_graph(e.cond_expr, g, child)
    id_dep_graph(e.then_expr, g, child)
    id_dep_graph(e.else_expr, g, child)
end

function id_dep_graph(e::EqualsOp, g, child)
    id_dep_graph(e.e1, g, child)
    id_dep_graph(e.e2, g, child)
end

function id_dep_graph(_::Categorical, _, _)
    # no op
end

function id_dep_graph(e::Int, g, child)
    # no op
end

function id_dep_graph(e::Identifier, g, child)
    if !isnothing(child)
        add_dep!(g, e, child)
    end
end

function id_dep_graph(e::DiceTuple, g, child)
    id_dep_graph(e.first, g, child)
    id_dep_graph(e.second, g, child)
end

############################################ 
# dependency graph functions
############################################

LightGraphs.SimpleDiGraph(g::IdDepGraph) =
    SimpleDiGraph(Edge.(g.edges))

LightGraphs.SimpleGraph(g::IdDepGraph) =
    SimpleGraph(Edge.(g.edges))

function plot(g::IdDepGraph; order = nothing)
    sg = SimpleDiGraph(g)
    if order == :program_order
        TikzGraphs.plot(sg)
    else
        if order == nothing
            labels = [g.id2int(i).symbol for i=1:g.num_ids]
        else 
            π = variable_order(g, order)
            πindex =  map(id -> g.id2int[id], π)
            labels = ["$(findfirst(isequal(i),πindex))" for i=1:g.num_ids]
        end
        TikzGraphs.plot(sg, labels)
    end
end

function plot_cut(g::IdDepGraph)
    sg = SimpleGraph(g)
    sgd = SimpleDiGraph(g) 
    sep_labels = Metis.separator(sg)
    labels = ["$(sep_labels[i])" for i=1:g.num_ids]
    TikzGraphs.plot(sgd, labels)
end
        
function LightGraphs.topological_sort_by_dfs(g::IdDepGraph)
    sg = SimpleDiGraph(g)
    π = topological_sort_by_dfs(sg)
    @assert length(π) == g.num_ids
    map(i -> g.id2int(i), π)
end

function metis_permutation(g::IdDepGraph)
    sg = SimpleGraph(g)
    π, _ = Metis.permutation(sg)
    @assert Set(π) == g.id2int.range
    map(i -> g.id2int(i), π)
end

function metis_cut(g::IdDepGraph)
    sg = SimpleGraph(g)
    sgd = SimpleDiGraph(g)
    
    sep_labels = Metis.separator(sg)
    
    seps = findall(isequal(3), sep_labels)
    clust1 = findall(isequal(1), sep_labels)
    clust2 = findall(isequal(2), sep_labels)
    
    sep_in = map(i -> inneighbors(sgd,i), seps)
    sep_out = map(i -> outneighbors(sgd,i), seps)
    sep_parents = unique(reduce(vcat,sep_in)) 
    sep_children = unique(reduce(vcat,sep_out))

    parents_clusters = sep_labels[sep_parents]
    children_clusters = sep_labels[sep_children]

    avg(x) = sum(x) / length(x)

    if avg(parents_clusters) < avg(children_clusters)    
        π = [clust1; seps ; clust2]
    else
        π = [clust2; seps ; clust1]
    end
    map(i -> g.id2int(i), π)
end

function variable_order(g, order)
    if order == :dfs
        topological_sort_by_dfs(g)
    elseif order == :dfs_rev
        reverse(topological_sort_by_dfs(g))
    elseif order == :metis_perm
        metis_permutation(g)
    elseif order == :metis_perm_rev
        reverse(metis_permutation(g))
    elseif order == :metis_cut
        metis_cut(g)
    else
        error("Unknown variable order: $order")
    end
end