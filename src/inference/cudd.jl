using CUDD

##################################
# CUDD Inference
##################################

function pr(x::Dist{Bool}, ::Cudd)
    mgr = CuddMgr() 
    bdd = compile(mgr, x)
    pr(mgr, bdd)
end

mutable struct CuddMgr
    cuddmgr::Ptr{Nothing}
    probs::Dict{Int,Float64}
end

function CuddMgr() 
    cudd_mgr = initialize_cudd()
    Cudd_DisableGarbageCollection(cudd_mgr) # note: still need to ref because CUDD can delete nodes without doing a GC pass
    mgr = CuddMgr(cudd_mgr, Dict{Int,Float64}())
    finalizer(mgr) do x
        Cudd_Quit(x.cuddmgr)
    end
end

function compile(mgr::CuddMgr, x::Dist{Bool})
    # TODO implement proper referencing and de-referencing of BDD nodes
    fl(x::Flip) = new_var(mgr, x.prob) 
    fi(n::DistAnd, call) = conjoin(mgr, call(n.x), call(n.y))
    fi(n::DistOr, call) = disjoin(mgr, call(n.x), call(n.y))
    fi(n::DistNot, call) = negate(mgr, call(n.x))
    foldup(x, fl, fi, Ptr{Nothing})
end

##################################
# Core CUDD API
##################################

function pr(mgr::CuddMgr, x::Ptr{Nothing})
    
    cache = Dict{Tuple{Ptr{Nothing},Bool},Float64}()
    t = constant(mgr, true)
    cache[(t,false)] = log(one(Float64))
    cache[(t,true)] = log(zero(Float64))
    
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
    
    logprob = rec(x, false)
    exp(logprob)
end

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

num_nodes(mgr::CuddMgr, xs::Vector{<:Ptr}; as_add=true) = begin
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
