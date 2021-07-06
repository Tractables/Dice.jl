# compile with indicators

comp_ind(p::String, mgr = default_manager())::ProbData = 
comp_ind(Dice.parse(DiceProgram,p), mgr)

comp_ind(p::DiceProgram, mgr = default_manager())::ProbData = 
    comp_ind(mgr, Context(mgr), p)

function comp_ind(mgr, ctx, p::DiceProgram)::ProbData
    g = id_dep_graph(p)
    π = variable_order(g, mgr.strategy.var_order)
    (mgr.strategy.debug >= 1) && println("Precompiling with order $π")
    for id in π
        (mgr.strategy.debug >= 10) && println("Precompiling $id")
        expr = g.id2expr[id]
        # precompile flips
        precompile_leafs(mgr, ctx, expr)
        # precompile indicators after flips - works better for topological orders?
        indicator = flip_indicator(mgr, expr)
        ctx.bindings[id.symbol] = indicator  
    end
    ctx.precompile_leafs = true
    circuit = ProbBool(mgr, true)
    for id in reverse(π)
        (mgr.strategy.debug >= 10) && println("Compiling $id")
        expr = g.id2expr[id]
        indicator = ctx.bindings[id.symbol]
        local_circuit = prob_equals(indicator, compile(mgr, ctx, expr))
        (mgr.strategy.debug >= 20) && println("Local circuit has size $(num_nodes(local_circuit))")
        circuit &= local_circuit
        (mgr.strategy.debug >= 20) && println("Circuit has size $(num_nodes(circuit))")
    end
    circuit
end

function flip_indicator(mgr, e)
    t = expr_type(e)
    if t[1] == DiceBool
        flip(mgr)
    elseif t[1] == DiceInt
        flip(mgr, ProbInt, t[2])
    else
        error("No indicator for $t")
    end
end