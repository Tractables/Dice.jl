abstract type DiceManager end

default_strategy() = (
    categorical = :bitwiseholtzen,
    branch_elim = :bdd
    )

default_manager() =
    CuddMgr(default_strategy())

struct Context
    bindings::Dict{String,ProbData}
    condition
end

default_context(mgr::DiceManager) = 
    Context(Dict{String,ProbData}(), nothing)
    
compile(p::String, mgr = default_manager())::ProbData = 
    compile(Dice.parse(DiceProgram,p), mgr)

compile(p::DiceProgram, mgr = default_manager())::ProbData = begin
    ctx = default_context(mgr)
    compile(mgr, ctx, p)
end 

compile(mgr, ctx, p::DiceProgram)::ProbData =
    compile(mgr, ctx, p.expr)

compile(mgr, _, b::Bool)::ProbBool =
    ProbBool(mgr, b ? true_node(mgr) :  false_node(mgr))


compile(mgr, _, f::Flip)::ProbBool = flip(mgr)

function compile(mgr, ctx, t::DiceTuple)::ProbTuple
    left = compile(mgr, ctx, t.first)
    right = compile(mgr, ctx, t.second)
    ProbTuple(mgr, left, right)
end
   
function compile(mgr, ctx, i::Int)::ProbInt
    get!(mgr.int_cache, i) do
        @assert i >= 0
        num_b = num_bits(i)
        bits = Vector{ProbBool}(undef, num_b)
        for bit_idx = 1:num_b
            b::Bool = i & 1
            @inbounds bits[bit_idx] = compile(mgr, ctx, b) 
            i = i >> 1
        end
        ProbInt(mgr, bits)
    end
end

num_bits(i) = ceil(Int,log2(i+1))

function compile(mgr, ctx, c::Categorical)::ProbInt
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
        max_val = maximum(((v,p),) -> v, vals)
        num_b = num_bits(max_val)
        bitvals = map(vals) do (v,p)
            (digits(Bool, v, base=2, pad=num_b), p)
        end
        bits = Vector{ProbBool}(undef, num_b)
        for digit = num_b:-1:1
            enum_contexts(bvs, i) = begin
                if i == digit
                    if all(((v,p),) -> !v[digit], bvs)
                        compile(mgr, ctx, false)
                    elseif all(((v,p),) -> v[digit], bvs)
                        compile(mgr, ctx, true)
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
    if mgr.strategy.branch_elim == :bdd
        cond = compile(mgr, ctx, ite_expr.cond_expr)
        if !issat(cond)
            # println("Condition $(ite_expr.cond_expr) is always false")
            compile(mgr, ctx, ite_expr.else_expr)
        elseif isvalid(cond)
            # println("Condition $(ite_expr.cond_expr) is always true")
            compile(mgr, ctx, ite_expr.then_expr)
        else
            then = compile(mgr, ctx, ite_expr.then_expr)
            elze = compile(mgr, ctx, ite_expr.else_expr)
            ite(cond, then, elze)
        end
    elseif mgr.strategy.branch_elim == :none
        cond = compile(mgr, ctx, ite_expr.cond_expr)
        then = compile(mgr, ctx, ite_expr.then_expr)
        elze = compile(mgr, ctx, ite_expr.else_expr)
        ite(cond, then, elze)
    else
        error("Unknown strategy $(mgr.strategy.branch_elim)")
    end
end

function compile(mgr, ctx, let_expr::LetExpr)::ProbData
    # Note: a recursive implementation can easily cause a StackOverflowError
    # so when e2 is also a let expression we should solve it iteratively
    # keep binding BDDs to identifiers until done
    while true
        id = let_expr.identifier.symbol
        @assert !haskey(ctx.bindings,id) "No support for reusing identifier symbols: $id"
        ctx.bindings[id] = compile(mgr, ctx, let_expr.e1)
        if let_expr.e2 isa LetExpr
            let_expr = let_expr.e2
        else
            break
        end
    end 
    # eventually e2 has to be a non-LetExpr, so compile it
    v = compile(mgr, ctx, let_expr.e2)::ProbData

    v
end