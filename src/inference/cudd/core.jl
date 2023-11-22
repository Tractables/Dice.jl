
##################################
# Core CUDD API
##################################

using CUDD

CuddNode = CUDD.DdNodePtr
CuddMgr = Ptr{Nothing}

# See this PR: https://github.com/sisl/CUDD.jl/pull/24

Fixed_Cudd_Not(node) =
    convert(Ptr{Nothing}, xor(convert(UInt,node), one(UInt)))

Fixed_Cudd_IsComplement(node) =
    isone(convert(UInt,node) & one(UInt))

Fixed_Cudd_Regular(node) =
    convert(Ptr{Nothing}, convert(UInt,node) & ~one(UInt))

not(x::CuddNode) = Fixed_Cudd_Not(x)

constant(mgr::CuddMgr, c:: Bool) =
    c ? Cudd_ReadOne(mgr) : Cudd_ReadLogicZero(mgr)

biconditional(mgr::CuddMgr, x, y) =
    rref(Cudd_bddXnor(mgr, x, y))

conjoin(mgr::CuddMgr, x, y) =
    rref(Cudd_bddAnd(mgr, x, y))

disjoin(mgr::CuddMgr, x, y) =
    rref(Cudd_bddOr(mgr, x, y))

negate(::CuddMgr, x) = 
    rref(not(x))

ite(mgr::CuddMgr, cond, then, elze) =
    rref(Cudd_bddIte(mgr, cond, then, elze))

new_var(mgr::CuddMgr) = rref(Cudd_bddNewVar(mgr))

isconstant(x) =
    isone(Cudd_IsConstant(x))

isliteral(::CuddMgr, x) =
    (!isconstant(x) &&
     isconstant(Cudd_T(x)) &&
     isconstant(Cudd_E(x)))

isposliteral(mgr::CuddMgr, x) =
    isliteral(mgr,x) && 
    (x === Cudd_bddIthVar(mgr, decisionvar(mgr,x)))

isnegliteral(mgr::CuddMgr, x) =
    isliteral(mgr,x) && 
    (x !== Cudd_bddIthVar(mgr, decisionvar(mgr,x)))

issat(mgr::CuddMgr, x) =
    x !== constant(mgr, false)

isvalid(mgr::CuddMgr, x) =
    x === constant(mgr, true)

num_bdd_nodes(mgr::CuddMgr, xs::Vector{<:Ptr}; as_add=true) = begin
    as_add && (xs = map(x -> rref(Cudd_BddToAdd(mgr, x)), xs))
    Cudd_SharingSize(xs, length(xs))
end

num_vars(mgr::CuddMgr, xs::Vector{<:Ptr}) =
    Cudd_VectorSupportSize(mgr, xs, length(xs))
        
num_vars(mgr::CuddMgr) =
    Cudd_ReadSize(mgr)

decisionvar(_::CuddMgr, x) =
    Cudd_NodeReadIndex(x)
mutable struct FILE end

dump_dot(mgr::CuddMgr, xs::Vector{<:Ptr}, filename; as_add=true) = begin
    # convert to ADDs in order to properly print terminals
    if as_add
        xs = map(x -> rref(Cudd_BddToAdd(mgr, x)), xs)
    end
    outfile = ccall(:fopen, Ptr{FILE}, (Cstring, Cstring), filename, "w")
    Cudd_DumpDot(mgr, length(xs), xs, C_NULL, C_NULL, outfile) 
    @assert ccall(:fclose, Cint, (Ptr{FILE},), outfile) == 0
    nothing
end

rref(x) = begin 
    ref(x)
    x
end


# Use high and low, instead of Cudd_T and Cudd_F, to encapsulate complement arcs
# and pretend they don't exist!

function high(x::CuddNode)
    @assert !isconstant(x)
    if Fixed_Cudd_IsComplement(x)
        not(Cudd_T(x))
    else
        Cudd_T(x)
    end
end

function low(x::CuddNode)
    @assert !isconstant(x)
    if Fixed_Cudd_IsComplement(x)
        not(Cudd_E(x))
    else
        Cudd_E(x)
    end
end

level(x::CuddNode) = Cudd_NodeReadIndex(x)

function level_traversal(f, root::CuddNode)
    level_to_nodes = []
    function see(x)
        isconstant(x) && return
        i = level(x) + 1  # add 1 to one-index, ensure always a valid index
        while length(level_to_nodes) < i
            push!(level_to_nodes, Set())
        end
        push!(level_to_nodes[i], x)
    end

    see(root)
    cur_level = 1
    while cur_level <= length(level_to_nodes)
        for node in level_to_nodes[cur_level]
            f(node)
            see(low(node))
            see(high(node))
        end
        cur_level += 1
    end
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