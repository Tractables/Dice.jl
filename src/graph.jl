using Bijections
using LightGraphs
using TikzGraphs

############################################ 
# graph representing dependencies between identifiers 
############################################
mutable struct IdDepGraph
    num_ids::Int
    id2int::Bijection{Identifier,Int}
    edges::Vector{Tuple{Int,Int}}
end

function IdDepGraph()
    IdDepGraph(0, Bijection{Identifier,Int}(), Vector{Tuple{Int,Int}}())
end

function add_identifier!(g::IdDepGraph, id::Identifier)
    next_int = (g.num_ids += 1)
    g.id2int[id] = next_int
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
    add_identifier!(g, e.identifier)
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
# plot dependency graphs 
############################################

function plot(g::IdDepGraph; labeled = true)
    sg = SimpleGraph(Edge.(g.edges))
    if labeled
        labels = [g.id2int(i).symbol for i=1:g.num_ids]
        TikzGraphs.plot(sg, labels)
    else
        TikzGraphs.plot(sg)
    end
end