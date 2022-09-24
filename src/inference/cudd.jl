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

function pr(cudd::Cudd, evidence, queries::Vector{JointQuery}; errors)
    mgr = CuddMgr(cudd.reordering_type)

    # TODO various optimizations
    # TODO variable order heuristics
    ccache = order_variables(mgr, evidence, queries, errors)
    
    # compile BDD for evidence
    evid_bdd = compile(mgr, evidence, ccache)
    evid_logp, pcache = logprobability(mgr, evid_bdd)

    # compile BDDs and infer probability of all errors
    prob_errors = ProbError[]
    for (cond, err) in errors
        cond_bdd = compile(mgr, cond, ccache)
        cond_bdd = conjoin(mgr, cond_bdd, evid_bdd)
        logp = logprobability(mgr, cond_bdd, pcache) - evid_logp
        isinf(logp) || push!(prob_errors, (exp(logp), err))
    end
    isempty(prob_errors) || throw(ProbException(prob_errors))

    # compile BDDs and infer probability for all queries
    results = map(queries) do query
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
                ifbdd, elsebdd = split(mgr, context, head, ccache)
                rec(ifbdd, cons(head => true, state), tail)
                rec(elsebdd, cons(head => false, state), tail)
            end
        end

        rec(evid_bdd, nil(), query.bits)
        @assert !isempty(states) "Cannot find possible worlds"
        [(Dict(state), p) for (state, p) in states]
    end

    if !isnothing(cudd.debug_info_ref)
        node_count = num_bdd_nodes(mgr, [ccache[bit] for query in queries for bit in query.bits])
        cudd.debug_info_ref[] = CuddDebugInfo(node_count)
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

function compile(mgr::CuddMgr, x)
    cache = Dict{Dist{Bool},Ptr{Nothing}}()
    bdd = compile(mgr, x, cache)
    bdd, cache
end

compile(mgr::CuddMgr, x::Bool, _) =
    constant(mgr, x)


function compile(mgr::CuddMgr, x::Dist{Bool}, cache)
    # TODO implement proper referencing and de-referencing of BDD nodes
    # TODO implement shortcuts for equivalence, etc.
    fl(x::Flip) = new_var(mgr, x.prob) 
    fi(n::DistAnd, call) = conjoin(mgr, call(n.x), call(n.y))
    fi(n::DistOr, call) = disjoin(mgr, call(n.x), call(n.y))
    fi(n::DistNot, call) = negate(mgr, call(n.x))
    foldup(x, fl, fi, Ptr{Nothing}, cache)
end

function order_variables(mgr, evidence, queries, errors)
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
    sort!(flips; by= f -> f.global_id)
    for flip in flips
        compile(mgr, flip, cache)
    end
    cache
end
    
function split(mgr::CuddMgr, context, test::AnyBool, cache)
    testbdd = compile(mgr, test, cache)
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

function logprobability(mgr::CuddMgr, x::Ptr{Nothing})
    cache = Dict{Tuple{Ptr{Nothing},Bool},Float64}()
    t = constant(mgr, true)
    cache[(t,false)] = log(one(Float64))
    cache[(t,true)] = log(zero(Float64))

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
    Cudd_Not(x)

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
