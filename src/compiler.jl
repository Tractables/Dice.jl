
const Binding = Dict{String,ProbData}

default_bindings() = Binding()

default_strategy() = (
    categorical = :bitwiseholtzen,
    branch_elim = :bdd
    )

compile(p::String, s = default_strategy())::ProbData = 
    compile(Dice.parse(DiceProgram,p), s)

compile(p::DiceProgram, s = default_strategy())::ProbData = 
    compile(default_manager(), default_bindings(), s, p)

compile(mgr, bind, s, p::DiceProgram)::ProbData =
    compile(mgr, bind, s, p.expr)

compile(mgr, _, _, b::Bool)::ProbBool =
    ProbBool(mgr, b ? true_node(mgr) :  false_node(mgr))


compile(mgr, _, _, f::Flip)::ProbBool = flip(mgr)

function compile(mgr, bind, s, t::DiceTuple)::ProbTuple
    left = compile(mgr, bind, s, t.first)
    right = compile(mgr, bind, s, t.second)
    ProbTuple(mgr, left, right)
end
   
function compile(mgr, bind, s, i::Int)::ProbInt
    get!(mgr.int_cache, i) do
        @assert i >= 0
        num_b = num_bits(i)
        bits = Vector{ProbBool}(undef, num_b)
        for bit_idx = 1:num_b
            b::Bool = i & 1
            @inbounds bits[bit_idx] = compile(mgr, bind, s, b) 
            i = i >> 1
        end
        ProbInt(mgr, bits)
    end
end

num_bits(i) = ceil(Int,log2(i+1))

function compile(mgr, bind, s, c::Categorical)::ProbInt
    if s.categorical == :sangbeamekautz
        vals = [(compile(mgr, bind, s, i-1), p) 
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
    elseif s.categorical == :bitwiseholtzen
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
                        compile(mgr, bind, s, false)
                    elseif all(((v,p),) -> v[digit], bvs)
                        compile(mgr, bind, s, true)
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
        error("Unknown strategy $(s.categorical)")
    end
end

function compile(mgr, bind, _, id::Identifier)::ProbData
    bind[id.symbol]
end

function compile(mgr, bind, s, eq::EqualsOp)::ProbBool
    c1 = compile(mgr, bind, s, eq.e1)
    c2 = compile(mgr, bind, s, eq.e2)
    prob_equals(c1, c2)
end

function compile(mgr, bind, s, ite_expr::Ite)::ProbData
    if s.branch_elim == :bdd
        cond = compile(mgr, bind, s, ite_expr.cond_expr)
        if !issat(cond)
            # println("Condition $(ite_expr.cond_expr) is always false")
            compile(mgr, bind, s, ite_expr.else_expr)
        elseif isvalid(cond)
            # println("Condition $(ite_expr.cond_expr) is always true")
            compile(mgr, bind, s, ite_expr.then_expr)
        else
            then = compile(mgr, bind, s, ite_expr.then_expr)
            elze = compile(mgr, bind, s, ite_expr.else_expr)
            ite(cond, then, elze)
        end
    elseif s.branch_elim == :none
        cond = compile(mgr, bind, s, ite_expr.cond_expr)
        then = compile(mgr, bind, s, ite_expr.then_expr)
        elze = compile(mgr, bind, s, ite_expr.else_expr)
        ite(cond, then, elze)
    else
        error("Unknown strategy $(s.branch_elim)")
    end
end

function compile(mgr, bind, s, let_expr::LetExpr)::ProbData
    # Note: a recursive implementation can easily cause a StackOverflowError
    # so when e2 is also a let expression we should solve it iteratively
    # keep binding BDDs to identifiers until done
    while true
        id = let_expr.identifier.symbol
        @assert !haskey(bind,id) "No support for reusing identifier symbols: $id"
        bind[id] = compile(mgr, bind, s, let_expr.e1)
        if let_expr.e2 isa LetExpr
            let_expr = let_expr.e2
        else
            break
        end
    end 
    # eventually e2 has to be a non-LetExpr, so compile it
    v = compile(mgr, bind, s, let_expr.e2)::ProbData

    v
end