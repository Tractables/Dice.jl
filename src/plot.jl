#==
using Graphs
using DirectedAcyclicGraphs
using TikzGraphs
using TikzPictures

function TikzGraphs.plot(x::Dist{Bool})
    n = DirectedAcyclicGraphs.num_nodes(x)
    labeling = label_nodes(x)
    g = SimpleDiGraph(n)
    nodelabels = ["?" for _ = 1:n]
    for (node, label) in labeling
        for i in children(node)
            add_edge!(g, label, labeling[i])
        end
        nodelabels[label] = shortlabel(node)
    end
    TikzGraphs.plot(g, nodelabels)
end

shortlabel(f::Flip) = 
    isnothing(f.name) ? "f$(f.global_id)($(f.prob))" : f.name
shortlabel(::DistAnd) = "⋀"
shortlabel(::DistOr) = "⋁"
shortlabel(::DistNot) = "¬"

TikzPictures.save(file, x::Dist) =
    TikzPictures.save(file, TikzGraphs.plot(x))
==#