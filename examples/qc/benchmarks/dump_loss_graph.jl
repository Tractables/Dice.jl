# run this at the bottom of main.jl to get a graphviz of the loss graph

bool_roots = Dice.bool_roots
LogPrExpander = Dice.LogPrExpander
expand_logprs = Dice.expand_logprs

@assert mgr.loss_mgr isa SimpleLossMgr

loss = mgr.loss_mgr.loss

l = LogPrExpander(WMC(BDDCompiler(bool_roots([loss]))))
eloss = expand_logprs(l, loss)

vals, derivs = differentiate(var_vals, Derivs(eloss => 1))
for (logpr, expanded) in l.cache
    vals[logpr] = vals[expanded]
    derivs[logpr] = if haskey(derivs, expanded) derivs[expanded] else 0 end
end

using Graphs
using DirectedAcyclicGraphs: isinner

function node_to_label(n)
    name = if isinner(n)
        last(Base.split(string(typeof(n)), "."))
    else
        replace(string(n), "\"" => "\\\"")
    end
    "$(name)\\n$(vals[n])\\n$(derivs[n])"
end

function dump_graph(path, node)
    g, nodes = Dice.to_graph(node)
    open(path, "w") do file
        println(file, "digraph G {")
        for (i, n) in enumerate(nodes)
            if n isa Var || n isa LogPr
                println(file, "  $(i) [fillcolor=lightcyan, style=filled];")
            end
            println(file, "  $(i) [label=\"$(node_to_label(n))\"];")
        end
        for e in edges(g)
            println(file, "  $(src(e)) -> $(dst(e));")
        end
        println(file, "}")
    end
end

dump_graph("loss.dot", loss)
dump_graph("eloss.dot", eloss)