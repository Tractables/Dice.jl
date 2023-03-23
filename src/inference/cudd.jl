using CUDD
using DataStructures: LinkedList, cons, nil

##################################
# CUDD Inference
##################################

struct CuddDebugInfo
    num_nodes::Integer
end

struct Cudd <: InferAlgo
    reordering_type::CUDD.Cudd_ReorderingType
    debug_info_ref::Union{Ref{CuddDebugInfo}, Nothing}
end

function Cudd(;reordering_type=CUDD.CUDD_REORDER_NONE, debug_info_ref=nothing)
    Cudd(reordering_type, debug_info_ref)
end

default_infer_algo() = Cudd()

function pr(cudd::Cudd, evidence, queries::Vector{JointQuery}, errors, dots)
    mgr = CuddMgr(cudd.reordering_type)

    num_uncompiled_parents = Dict{Dist{Bool}, Int}()
    seen = Set{Dist{Bool}}()
    for root in Iterators.flatten((
        Iterators.flatten(query.bits for query in queries),
        (err[1] for err in errors),
        [evidence],
        Iterators.flatten(xs for (xs, filename) in dots),
    ))
        foreach(root) do node
            isa(node, Bool) && return
            (node ∈ seen) && return
            push!(seen, node)

            for child in unique(children(node))
                num_uncompiled_parents[child] = get(num_uncompiled_parents, child, 0) + 1
            end
        end
    end

    # TODO various optimizations
    # TODO variable order heuristics
    ccache = order_variables(mgr, evidence, queries, errors, dots, num_uncompiled_parents)
    pcache = logprobability_cache(mgr)

    # compile BDDs and infer probability of all errors
    prob_errors = ProbError[]
    for (cond, err) in errors
        cond_bdd = compile(mgr, cond, ccache, num_uncompiled_parents)
        logp = logprobability(mgr, cond_bdd, pcache)
        isinf(logp) || push!(prob_errors, (exp(logp), err))
    end
    isempty(prob_errors) || throw(ProbException(prob_errors))

    for (xs, filename) in dots
        xs = [compile(mgr, x, ccache, num_uncompiled_parents) for x in xs]
        dump_dot(mgr, xs, filename)
    end

    # compile BDD for evidence
    evid_bdd = compile(mgr, evidence, ccache, num_uncompiled_parents)
    evid_logp = logprobability(mgr, evid_bdd, pcache)


    # compile BDDs and infer probability for all queries
    results = map(queries) do query

        # TODO should query bits be made unique to save time?
        
        states = Pair{LinkedList, Float64}[]

        rec(context, state, rembits) = begin
            issat(mgr, context) || return
            if isempty(rembits)
                logpcontext = logprobability(mgr, context, pcache)
                p = exp(logpcontext - evid_logp)
                push!(states, state => p)
            else
                head = rembits[1]
                tail = @view rembits[2:end]
                ifbdd, elsebdd = split(mgr, context, head, ccache, num_uncompiled_parents)
                rec(ifbdd, cons(head => true, state), tail)
                rec(elsebdd, cons(head => false, state), tail)
            end
        end

        if issat(mgr, evid_bdd) && isempty(query.bits) 
            push!(states, nil() => 1.0)
        else
            rec(evid_bdd, nil(), query.bits)
        end
        @assert !isempty(states) "Cannot find any possible worlds"
        [(Dict(state), p) for (state, p) in states]
    end

    if !isnothing(cudd.debug_info_ref)
        node_count = num_bdd_nodes(mgr, [
            ccache[root]
            for root in Iterators.flatten((
                Iterators.flatten(query.bits for query in queries),
                (err[1] for err in errors),
                [evidence],
            ))
            if !isa(root, Bool)
        ])
        cudd.debug_info_ref[] = CuddDebugInfo(node_count)
    end

    for nup in values(num_uncompiled_parents)
        @assert nup == 0 "Dereferences are likely suboptimal because num_uncompiled_parents was initialized improperly."
    end

    results
end

mutable struct CuddMgr
    cuddmgr::Ptr{Nothing}
    probs::Dict{Int,Float64}
end

function CuddMgr(reordering_type::CUDD.Cudd_ReorderingType)
    cudd_mgr = initialize_cudd()
    Cudd_DisableGarbageCollection(cudd_mgr) # note: still need to ref because CUDD can delete nodes without doing a GC pass
    reordering_type == CUDD.CUDD_REORDER_NONE || Cudd_AutodynEnable(cudd_mgr, reordering_type)
    mgr = CuddMgr(cudd_mgr, Dict{Int,Float64}())
    finalizer(mgr) do x
        Cudd_Quit(x.cuddmgr)
    end
end

compile(mgr::CuddMgr, x::Bool, _, _) =
    constant(mgr, x)


function compile(mgr::CuddMgr, x::Dist{Bool}, cache, num_uncompiled_parents)
    # TODO implement shortcuts for equivalence, etc.
    function mark_as_compiled(node)
        for child in unique(children(node))
            num_uncompiled_parents[child] -= 1
            @assert num_uncompiled_parents[child] >= 0
            if num_uncompiled_parents[child] == 0
                # Cudd_RecursiveDeref(mgr.cuddmgr, cache[child])
            end
        end
    end

    fl(n::Flip) = begin
        if !haskey(cache, n)
            cache[n] = new_var(mgr, n.prob)
        end
        cache[n]
    end

    fi(n::DistAnd, call) = begin
        if !haskey(cache, n)
            call(n.x)
            call(n.y)
            cache[n] = conjoin(mgr, cache[n.x], cache[n.y])
            mark_as_compiled(n)
        end
        cache[n]
    end

    fi(n::DistOr, call) = begin
        if !haskey(cache, n)
            call(n.x)
            call(n.y)
            cache[n] = disjoin(mgr, cache[n.x], cache[n.y])
            mark_as_compiled(n)
        end
        cache[n]
    end

    fi(n::DistNot, call) = begin
        if !haskey(cache, n)
            call(n.x)
            cache[n] = negate(mgr, cache[n.x])
            mark_as_compiled(n)
        end
        cache[n]
    end

    foldup(x, fl, fi, Ptr{Nothing})
end

function order_variables(mgr, evidence, queries, errors, dots, num_uncompiled_parents)
    cache = Dict{Dist{Bool},Ptr{Nothing}}()
    flips = Vector{Flip}()
    seen = Dict{DAG,Nothing}()
    see_flip(f) = push!(flips, f)
    noop = Returns(nothing)
    evidence isa Bool || foreach(evidence, see_flip, noop, seen)
    for query in queries, bit in query.bits
        foreach(bit, see_flip, Returns(nothing), seen)
    end
    for (cond, _) in errors
        cond isa Bool || foreach(cond, see_flip, noop, seen)
    end
    for (xs, filename) in dots, bit in xs
        bit isa Bool || foreach(bit, see_flip, Returns(nothing), seen)
    end
    sort!(flips; by= f -> f.global_id)
    for flip in flips
        compile(mgr, flip, cache, num_uncompiled_parents)
    end
    cache
end
    
function split(mgr::CuddMgr, context, test::AnyBool, cache, num_uncompiled_parents)
    testbdd = compile(mgr, test, cache, num_uncompiled_parents)
    ifbdd = conjoin(mgr, context, testbdd)
    if ifbdd === context
        return (context, constant(mgr, false))
    elseif !issat(mgr, ifbdd)
        return (constant(mgr, false), context)
    else
        nottestbdd = negate(mgr, testbdd)
        elsebdd = conjoin(mgr, context, nottestbdd)
        return (ifbdd, elsebdd)
    end
end

function logprobability_cache(mgr::CuddMgr)
    cache = Dict{Tuple{Ptr{Nothing},Bool},Float64}()
    t = constant(mgr, true)
    cache[(t,false)] = log(one(Float64))
    cache[(t,true)] = log(zero(Float64))
    cache
end

function logprobability(mgr::CuddMgr, x::Ptr{Nothing})
    cache = logprobability_cache(mgr)
    logp = logprobability(mgr, x, cache)
    logp, cache
end

function logprobability(mgr::CuddMgr, x::Ptr{Nothing}, cache)
    rec(y, c) = 
        if Cudd_IsComplement(y)
            rec(Cudd_Regular(y), !c)   
        else get!(cache, (y,c)) do 
                v = decisionvar(mgr,y)
                prob = mgr.probs[v]
                a = log(prob) + rec(Cudd_T(y), c)
                b = log(1.0-prob) + rec(Cudd_E(y), c)
                if (!isfinite(a))
                    b
                elseif (!isfinite(b))
                    a
                else
                    max(a,b) + log1p(exp(-abs(a-b)))
                end
            end
        end
    
    rec(x, false)
end

probability(mgr::CuddMgr, x::Ptr{Nothing}) =
    exp(logprobability(mgr, x))

##################################
# Core CUDD API
##################################

constant(mgr::CuddMgr, c:: Bool) = 
    c ? Cudd_ReadOne(mgr.cuddmgr) : Cudd_ReadLogicZero(mgr.cuddmgr)

biconditional(mgr::CuddMgr, x, y) =
    rref(Cudd_bddXnor(mgr.cuddmgr, x, y))

conjoin(mgr::CuddMgr, x, y) =
    rref(Cudd_bddAnd(mgr.cuddmgr, x, y))

disjoin(mgr::CuddMgr, x, y) =
    rref(Cudd_bddOr(mgr.cuddmgr, x, y))

negate(::CuddMgr, x) = 
    rref(Cudd_Not(x))

ite(mgr::CuddMgr, cond, then, elze) =
    rref(Cudd_bddIte(mgr.cuddmgr, cond, then, elze))

new_var(mgr::CuddMgr, prob) = begin
    x = rref(Cudd_bddNewVar(mgr.cuddmgr))
    mgr.probs[decisionvar(mgr, x)] = prob
    x
end

function Base.show(io::IO, mgr::CuddMgr, x) 
    if !issat(mgr, x)
        print(io, "(false)") 
    elseif isvalid(mgr, x)
        print(io, "(true)")
    elseif isposliteral(mgr, x)
        print(io, "(f$(decisionvar(mgr, x)))")
    elseif isnegliteral(mgr, x)
        print(io, "(-f$(decisionvar(mgr, x)))")
    else    
        print(io, "@$(hash(x)÷ 10000000000000)")
    end
end

function Base.show(io::IO, x::CuddMgr) 
    print(io, "$(typeof(x))@$(hash(x)÷ 10000000000000)")
end

isconstant(x) =
    isone(Cudd_IsConstant(x))

isliteral(::CuddMgr, x) =
    (!isconstant(x) &&
     isconstant(Cudd_T(x)) &&
     isconstant(Cudd_E(x)))

isposliteral(mgr::CuddMgr, x) =
    isliteral(mgr,x) && 
    (x === Cudd_bddIthVar(mgr.cuddmgr, decisionvar(mgr,x)))

isnegliteral(mgr::CuddMgr, x) =
    isliteral(mgr,x) && 
    (x !== Cudd_bddIthVar(mgr.cuddmgr, decisionvar(mgr,x)))

issat(mgr::CuddMgr, x) =
    x !== constant(mgr, false)

isvalid(mgr::CuddMgr, x) =
    x === constant(mgr, true)

num_bdd_nodes(mgr::CuddMgr, xs::Vector{<:Ptr}; as_add=true) = begin
    as_add && (xs = map(x -> rref(Cudd_BddToAdd(mgr.cuddmgr, x)), xs))
    Cudd_SharingSize(xs, length(xs))
end

num_vars(mgr::CuddMgr, xs::Vector{<:Ptr}) =
    Cudd_VectorSupportSize(mgr.cuddmgr, xs, length(xs))
        
num_vars(mgr::CuddMgr) =
    Cudd_ReadSize(mgr.cuddmgr)

decisionvar(_::CuddMgr, x) =
    Cudd_NodeReadIndex(x)
mutable struct FILE end

dump_dot(mgr::CuddMgr, xs::Vector{<:Ptr}, filename; as_add=true) = begin
    # convert to ADDs in order to properly print terminals
    if as_add
        xs = map(x -> rref(Cudd_BddToAdd(mgr.cuddmgr, x)), xs)
    end
    outfile = ccall(:fopen, Ptr{FILE}, (Cstring, Cstring), filename, "w")
    Cudd_DumpDot(mgr.cuddmgr, length(xs), xs, C_NULL, C_NULL, outfile) 
    @assert ccall(:fclose, Cint, (Ptr{FILE},), outfile) == 0
    nothing
end

rref(x) = begin 
    ref(x)
    x
end
