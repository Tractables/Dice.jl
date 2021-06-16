
const Binding = Dict{String,ProbData}

default_bindings() = Binding()
default_strategy() = (
    categorical = :bitwiseholtzen,
    branch_elim = :bdd
    )

compile(p::String, s = default_strategy()) = 
    compile(Dice.parse(DiceProgram,p), s)

compile(p::DiceProgram, s = default_strategy()) = 
    compile(default_manager(), default_bindings(), s, p)

compile(mgr, bind, s, p::DiceProgram) =
    compile(mgr, bind, s, p.expr)

compile(mgr, _, _, b::Bool) =
    ProbBool(mgr, b ? true_node(mgr) :  false_node(mgr))


compile(mgr, _, _, f::Flip) = flip(mgr)

function compile(mgr, bind, s, t::Tuple{X,Y}) where {X,Y}
    left = compile(mgr, bind, s, t[1])
    # println("Compiled LHS for tuple ($(t[1]),_)")
    right = compile(mgr, bind, s, t[2])
    # println("Compiled all of tuple $t")
    ProbTuple(mgr, left, right)
end
   
function compile(mgr, bind, s, i::Int)
    @assert i >= 0
    num_bits = ceil(Int,log2(i+1))
    bits = Vector{ProbBool}(undef, num_bits)
    for bit_idx = 1:num_bits
        b::Bool = i & 1
        @inbounds bits[bit_idx] = compile(mgr, bind, s, b) 
        i = i >> 1
    end
    ProbInt(mgr, bits)
end

function compile(mgr, bind, s, c::Categorical)
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
        maxval = maximum(((v,p),) -> v, vals)
        num_digits = length(digits(Bool, maxval, base=2)) #lazy
        bitvals = map(vals) do (v,p)
            (digits(Bool, v, base=2, pad=num_digits), p)
        end
        bits = Vector{ProbBool}(undef, num_digits)
        for digit = num_digits:-1:1
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
            bits[digit] = enum_contexts(bitvals, num_digits)
        end
        ProbInt(mgr, bits)
    else
        error("Unknown strategy $(s.categorical)")
    end
end

function compile(mgr, bind, _, id::Identifier)
    bind[id.symbol]
end

function compile(mgr, bind, s, eq::EqualsOp)
    c1 = compile(mgr, bind, s, eq.e1)
    c2 = compile(mgr, bind, s, eq.e2)
    prob_equals(c1, c2)
end

function compile(mgr, bind, s, ite_expr::Ite)
    if s.branch_elim == :bdd
        cond = compile(mgr, bind, s, ite_expr.cond_expr)
        if !issat(cond)
            compile(mgr, bind, s, ite_expr.else_expr)
        elseif isvalid(cond)
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

function compile(mgr, bind, s, let_expr::LetExpr)
    c1 = compile(mgr, bind, s, let_expr.e1)
    id = let_expr.identifier.symbol
    @assert !haskey(bind,id)
    bind[id] = c1
    # println("Compiled $id")
    c2 = compile(mgr, bind, s, let_expr.e2)
    delete!(bind, id)
    c2
end
