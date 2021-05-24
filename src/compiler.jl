
const Binding = Dict{String,ProbData}

default_bindings() = Binding()

compile(p::String) = 
    compile(Dice.parse(DiceProgram,p))

compile(p::DiceProgram) = 
    compile(default_manager(), default_bindings(), p)

compile(mgr, bind, p::DiceProgram) =
    compile(mgr, bind, p.expr)

compile(mgr, _, b::Bool) =
    ProbBool(mgr, b ? true_node(mgr) :  false_node(mgr))

function compile(mgr, bind, t::Tuple{X,Y}) where {X,Y}
    left = compile(mgr, bind, t[1])
    right = compile(mgr, bind, t[2])
    ProbTuple(mgr, left, right)
end
   
function compile(mgr, _, i::Int)
    @assert i >= 0
    num_bits = ceil(Int,log2(i+1))
    bits = Vector{ProbBool}(undef, num_bits)
    for bit_idx = 1:num_bits
        b::Bool = i & 1
        @inbounds bits[bit_idx] = compile(mgr, bind, b) 
        i = i >> 1
    end
    ProbInt(mgr, bits)
end

function compile(mgr, bind,  c::Categorical)
    # code for exploiting determinism commented out
    vals = collect(enumerate(c.probs))
    pos_vals = vals # filter(x -> !iszero(x[2]), vals)
    compile_val(v) = compile(mgr, bind, v[1]-1)
    # if length(pos_vals) == 1
    #     compile_val(pos_vals[1])
    # else
        choose(x,y) = ite(flip(mgr), x, y)
        mapreduce(compile_val, choose, pos_vals)
    # end
end

function compile(mgr, bind, id::Identifier)
    bind[id.symbol]
end

function compile(mgr, bind, eq::EqualsOp)
    c1 = compile(mgr, bind, eq.e1)
    c2 = compile(mgr, bind, eq.e2)
    prob_equals(c1, c2)
end

function compile(mgr, bind, ite_expr::Ite)
    # cond = compile(mgr, bind, ite_expr.cond_expr)
    # # optimize for case when cond is deterministic?
    # if !issat(cond)
    #     compile(mgr, bind, ite_expr.else_expr)
    # elseif isvalid(cond)
    #     compile(mgr, bind, ite_expr.then_expr)
    # else
    #     then = compile(mgr, bind, ite_expr.then_expr)
    #     elze = compile(mgr, bind, ite_expr.else_expr)
    #     ite(cond, then, elze)
    # end
    cond = compile(mgr, bind, ite_expr.cond_expr)
    then = compile(mgr, bind, ite_expr.then_expr)
    elze = compile(mgr, bind, ite_expr.else_expr)
    ite(cond, then, elze)
end

function compile(mgr, bind, let_expr::LetExpr)
    c1 = compile(mgr, bind, let_expr.e1)
    id = let_expr.identifier.symbol
    @assert !haskey(bind,id)
    bind[id] = c1
    c2 = compile(mgr, bind, let_expr.e2)
    delete!(bind, id)
    c2
end