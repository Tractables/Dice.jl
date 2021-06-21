# non-deterministic reachability analysis

# this is fast on some bayesian networks, but very slow on others (munin).
# consider more automatic wekaenings of the analysis/ upper bounds on the support

support(p::String, mgr = default_manager()) = 
    support(Dice.parse(DiceProgram,p), mgr)

function support(p::DiceProgram, mgr = default_manager())
    ctx = Context(mgr)
    # initially there are no constraints on the support
    supp = true_constant(mgr)
    supp = support(mgr, ctx, supp, p.expr)
    return supp, ctx.bindings
end

function support(mgr, _, _, x::ProbInt, i::Int)
    prob_equals(x,ProbInt(mgr, i))
end

function support(mgr, _, _, x::ProbInt, c::Categorical)
    vals = [ProbInt(mgr, i-1) 
            for (i,p) in enumerate(c.probs) if !iszero(p)]
    mapfoldl(|,vals) do v
        prob_equals(x,v)
    end
end

function support(mgr, ctx, supp, x::ProbInt, ite_expr::Ite)
    guard = compile_bounds(mgr, ctx, supp, ite_expr.cond_expr)
    then = support(mgr, ctx, supp, x, ite_expr.then_expr)
    elze = support(mgr, ctx, supp, x, ite_expr.else_expr)
    return ite(guard, then, elze)
    # then | elze
end

function support(mgr, ctx, supp, let_expr::LetExpr)
    # this code assumes the type is integer, lazy
    id = let_expr.identifier.symbol
    println("Analyzing support for $id")
    nb = num_bits(let_expr.e1)
    x = flip(mgr, ProbInt, nb)
    @assert !haskey(ctx.bindings,id) "No support for reusing identifier symbols: $id"
    ctx.bindings[id] = x

    # now constrain the values of x by looking at e1
    supp &= support(mgr, ctx, supp, x, let_expr.e1)
    println("Nodes: $(num_nodes(supp)), Vars: $(num_flips(supp))")

    # collect supports in e2
    supp &= support(mgr, ctx, supp, let_expr.e2)
    supp
end

function support(mgr, ctx, supp, let_expr::Identifier)
    # lazy, to implement later
    ProbBool(mgr, true)
end

function support(mgr, ctx, supp, let_expr::DiceTuple)
    # lazy, to implement later
    ProbBool(mgr, true)
end

# not sure what the general case should be (something with upper and lower bounds) 
# but of equality of identifiers and constants, it should behave like normal compilation    
function compile_bounds(mgr, ctx, supp, eq::EqualsOp)
    c1 = compile_bounds(mgr, ctx, supp, eq.e1)
    c2 = compile_bounds(mgr, ctx, supp, eq.e2)
    prob_equals(c1, c2)
end

function compile_bounds(mgr, ctx, supp, id::Identifier)
    ctx.bindings[id.symbol]
end

function compile_bounds(mgr, ctx, supp, x::Int)
    ProbInt(mgr, x)
end


