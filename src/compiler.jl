abstract type DiceManager end

############################################ 
############################################

default_strategy() = (
    categorical = :bitwiseholtzen,
    branch_elim = :guard_bdd,
    include_indicators = false,
    var_order = :program_order,
    debug = 0
)

default_manager() =
    CuddMgr(default_strategy())

mutable struct Context
    bindings::Dict{String,ProbData}
    condition::ProbBool
    indicators::Dict{String,ProbData}
    global_compilation::ProbBool
    precompile_cache::Dict{DiceExpr, ProbData}
    precompile_leafs::Bool
end

function Context(mgr::DiceManager)
    bindings = Dict{String,ProbData}()
    condition  = ProbBool(mgr, true)
    indicators = Dict{String,ProbData}()
    global_compilation = ProbBool(mgr, true) 
    precompile_cache = Dict{DiceExpr, ProbData}()
    precompile_leafs = false
    Context(bindings, condition, indicators, global_compilation, precompile_cache, precompile_leafs)
end

############################################
############################################

compile(p::String, mgr = default_manager())::ProbData = 
    compile(Dice.parse(DiceProgram,p), mgr)

compile(p::DiceProgram, mgr = default_manager())::ProbData = 
    compile(mgr, Context(mgr), p)


function compile(mgr, ctx, p::DiceProgram)::ProbData
    if mgr.strategy.var_order != :program_order
        g = id_dep_graph(p)
        π = variable_order(g, mgr.strategy.var_order)
        for id in π
            precompile_leafs(mgr, ctx, g.id2expr[id])
        end
        ctx.precompile_leafs = true
    end
    compile(mgr, ctx, p.expr)
end

compile(mgr, _, b::Bool) =
    ProbBool(mgr, b)

function compile(mgr, ctx, f::Flip)::ProbBool 
    if ctx.precompile_leafs
        # if haskey(ctx.precompile_cache, f)
            return ctx.precompile_cache[f]
        # end
    end
    if isone(f.prob)
        compile(mgr, ctx, true)
    elseif iszero(f.prob)
        compile(mgr, ctx, false)
    else
        flip(mgr)
    end
end
  
compile(mgr, _, i::Int)=
    ProbInt(mgr, i)

function compile(mgr, ctx, t::DiceTuple)::ProbTuple
    left = compile(mgr, ctx, t.first)
    right = compile(mgr, ctx, t.second)
    ProbTuple(mgr, left, right)
end

function compile(mgr, ctx, c::Categorical)::ProbInt
    if ctx.precompile_leafs
        # if haskey(ctx.precompile_cache, c)
            return ctx.precompile_cache[c]
        # end
    end
    if mgr.strategy.categorical == :sangbeamekautz
        vals = [(compile(mgr, ctx, i-1), p) 
                    for (i,p) in enumerate(c.probs) if !iszero(p)]
        cvals(vs) = begin
            v1 = vs[1][1]
            if length(vs) == 1
                v1
            else
                test = flip(mgr)
                elze = cvals(vs[2:end])
                ite(test, v1, elze)
            end
        end
        cvals(vals)
    elseif mgr.strategy.categorical == :bitwiseholtzen
        vals = [(i-1, p) for (i,p) in enumerate(c.probs) if !iszero(p)]
        num_b = num_bits(c)
        bitvals = map(vals) do (v,p)
            (digits(Bool, v, base=2, pad=num_b), p)
        end
        bits = Vector{ProbBool}(undef, num_b)
        for digit = num_b:-1:1
            enum_contexts(bvs, i) = begin
                if i == digit
                    if all(((v,p),) -> !v[digit], bvs)
                        ProbBool(mgr, false)
                    elseif all(((v,p),) -> v[digit], bvs)
                        ProbBool(mgr, true)
                    else
                        flip(mgr)
                    end
                else
                    test = !bits[i] # dice tries false first
                    bvs0 = filter(((v,p),) -> !v[i], bvs)
                    then = enum_contexts(bvs0, i-1)
                    bvs1 = filter(((v,p),) -> v[i], bvs)
                    elze = enum_contexts(bvs1, i-1)
                    ite(test, then, elze)
                end
            end
            bits[digit] = enum_contexts(bitvals, num_b)
        end
        ProbInt(mgr, bits)
    else
        error("Unknown strategy $(mgr.strategy.categorical)")
    end
end

function compile(_, ctx, id::Identifier)::ProbData
    ctx.bindings[id.symbol]
end

function compile(mgr, ctx, eq::EqualsOp)::ProbBool
    c1 = compile(mgr, ctx, eq.e1)
    c2 = compile(mgr, ctx, eq.e2)
    prob_equals(c1, c2)
end

function compile(mgr, ctx, ite_expr::Ite)::ProbData
    yield()
    if mgr.strategy.branch_elim == :nested_guard_bdd
        flatten_ite(c,expr) = (issat(c) ? [(c,expr)] : []) # base case
        flatten_ite(c,expr::Ite) = begin
            if issat(c) 
                # let, otherwise guard gets overwritten by the recursion...
                let guard = compile(mgr, ctx, expr.cond_expr), 
                    f1 = flatten_ite(c & guard, expr.then_expr),
                    f2 = flatten_ite(c & !guard, expr.else_expr)
                    if issat(guard) && isempty(f1)
                        println("$expr then branch not reachable")
                        println()
                    end
                    if !isvalid(guard) && isempty(f2)
                        println("$expr else branch not reachable")
                        println()
                    end
                    [f1; f2]
                end
            else
                []
            end
        end
        cases = flatten_ite(ProbBool(mgr, true), ite_expr)
        init = compile(mgr, ctx, cases[1][2]) # then/then/* branch
        foldl(cases[2:end]; init) do elze, case
            c, e = case
            case_val = compile(mgr, ctx, e) 
            ite(c, case_val, elze)
        end
    else
        guard = compile(mgr, ctx, ite_expr.cond_expr)
        if mgr.strategy.branch_elim == :path_bdd ||
            mgr.strategy.branch_elim == :guard_bdd
            if !issat(guard)
                return compile(mgr, ctx, ite_expr.else_expr)
            elseif isvalid(guard)
                return compile(mgr, ctx, ite_expr.then_expr)
            else
                if mgr.strategy.branch_elim == :path_bdd
                    precond = ctx.condition
                    @assert issat(precond)
                    thencond = precond & guard
                    elzecond = precond & !guard
                    if !issat(thencond)
                        ctx.condition = elzecond
                        return compile(mgr, ctx, ite_expr.else_expr)
                    elseif !issat(elzecond)
                        ctx.condition = thencond
                        return compile(mgr, ctx, ite_expr.then_expr)
                    else
                        ctx.condition = thencond
                        then = compile(mgr, ctx, ite_expr.then_expr)
                        ctx.condition = elzecond
                        elze = compile(mgr, ctx, ite_expr.else_expr)
                    end
                    ctx.condition = precond
                else
                    then = compile(mgr, ctx, ite_expr.then_expr)
                    elze = compile(mgr, ctx, ite_expr.else_expr)    
                end
                return ite(guard, then, elze)
            end
        elseif mgr.strategy.branch_elim == :none
            then = compile(mgr, ctx, ite_expr.then_expr)
            elze = compile(mgr, ctx, ite_expr.else_expr)
            return ite(guard, then, elze)
        else
            error("Unknown strategy $(mgr.strategy.branch_elim)")
        end
    end
end

function compile(mgr, ctx, let_expr::LetExpr)::ProbData
    # Note: a recursive implementation can easily cause a StackOverflowError
    # so when e2 is also a let expression we should solve it iteratively
    # keep binding BDDs to identifiers until done
    i = 0
    while true
        yield()
        id = let_expr.identifier.symbol
        i += 1
        (mgr.strategy.debug >= 1) && print("Compiling $(i)th let $id")
        @assert !haskey(ctx.bindings,id) "No support for reusing identifier symbols: $id"
        if mgr.strategy.include_indicators
            nb = num_bits(let_expr.e1)
            x = flip(mgr, ProbInt, nb)
            @assert !haskey(ctx.indicators,id) "No support for reusing identifier symbols: $id"
            ctx.indicators[id] = x
        end
        ctx.bindings[id] = compile(mgr, ctx, let_expr.e1)
        if mgr.strategy.include_indicators
            ctx.global_compilation &= 
                prob_equals(x, ctx.bindings[id])
            println("Global compilation has size $(num_nodes(ctx.global_compilation))")
        end
        (mgr.strategy.debug >= 1) && println(" into $(num_nodes(ctx.bindings[id])) nodes")
        if let_expr.e2 isa LetExpr
            let_expr = let_expr.e2
        else
            break
        end
    end 
    # eventually e2 has to be a non-LetExpr, so compile it
    compile(mgr, ctx, let_expr.e2)::ProbData
end

############################################
############################################

function precompile_leafs(mgr, ctx, e::LetExpr)
    # skip e1 because it is associated with a different id
    precompile_leafs(mgr, ctx, e.e2)
end

function precompile_leafs(mgr, ctx, e::Ite)
    precompile_leafs(mgr, ctx, e.cond_expr)
    precompile_leafs(mgr, ctx, e.then_expr)
    precompile_leafs(mgr, ctx, e.else_expr)
end

function precompile_leafs(mgr, ctx, e::EqualsOp)
    precompile_leafs(mgr, ctx, e.e1)
    precompile_leafs(mgr, ctx, e.e2)
end

function precompile_leafs(mgr, ctx, e::Union{Int,Bool,Identifier})
    # no op
end

function precompile_leafs(mgr, ctx, e::Union{Flip,Categorical})
    ctx.precompile_cache[e] = compile(mgr, ctx, e)
end

function precompile_leafs(mgr, ctx, e::DiceTuple)
    precompile_leafs(mgr, ctx, e.first)
    precompile_leafs(mgr, ctx, e.second)
end
