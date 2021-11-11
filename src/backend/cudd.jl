# compilation backend that uses CUDD

using CUDD

mutable struct CuddMgr <: DiceManager
    cuddmgr::Ptr{Nothing}
end

function CuddMgr() 
    cudd_mgr = initialize_cudd()
    Cudd_DisableGarbageCollection(cudd_mgr) # note: still need to ref because CUDD can delete nodes without doing a GC pass
    mgr = CuddMgr(cudd_mgr)
    finalizer(mgr) do x
        Cudd_Quit(x.cuddmgr)
    end
end

function Base.show(io::IO, mgr::CuddMgr, x) 
    if !issat(mgr, x)
        print(io, "(false)") 
    elseif isvalid(mgr, x)
        print(io, "(true)")
    elseif isposliteral(mgr, x)
        print(io, "(f$(firstvar(mgr, x)))")
    elseif isnegliteral(mgr, x)
        print(io, "(-f$(firstvar(mgr, x)))")
    else    
        print(io, "@$(hash(x)÷ 10000000000000)")
    end
end

function Base.show(io::IO, x::CuddMgr) 
    print(io, "$(typeof(x))@$(hash(x)÷ 10000000000000)")
end

@inline true_val(mgr::CuddMgr) = 
    Cudd_ReadOne(mgr.cuddmgr)

@inline false_val(mgr::CuddMgr) = 
    Cudd_ReadLogicZero(mgr.cuddmgr)

@inline isliteral(mgr::CuddMgr, x) =
    num_nodes(mgr, [x]) == 3

@inline isposliteral(mgr::CuddMgr, x) =
    isliteral(mgr,x) && 
    (x === Cudd_bddIthVar(mgr.cuddmgr, firstvar(mgr,x)))

@inline isnegliteral(mgr::CuddMgr, x) =
    isliteral(mgr,x) && 
    (x !== Cudd_bddIthVar(mgr.cuddmgr, firstvar(mgr,x)))

@inline firstvar(_::CuddMgr, x) =
    Cudd_NodeReadIndex(x)

@inline rref(x) = begin 
    ref(x)
    x
end

@inline biconditional(mgr::CuddMgr, x, y) =
    rref(Cudd_bddXnor(mgr.cuddmgr, x, y))

@inline conjoin(mgr::CuddMgr, x, y) =
    rref(Cudd_bddAnd(mgr.cuddmgr, x, y))

@inline disjoin(mgr::CuddMgr, x, y) =
    rref(Cudd_bddOr(mgr.cuddmgr, x, y))

@inline negate(mgr::CuddMgr, x) =
    # workaround until https://github.com/sisl/CUDD.jl/issues/16 is fixed
    rref(biconditional(mgr, x, false_val(mgr)))

@inline ite(mgr::CuddMgr, cond, then, elze) =
    rref(Cudd_bddIte(mgr.cuddmgr, cond, then, elze))

@inline issat(mgr::CuddMgr, x) =
    x !== false_val(mgr)

@inline isvalid(mgr::CuddMgr, x) =
    x === true_val(mgr)

@inline new_var(mgr::CuddMgr, prob) =
    rref(Cudd_bddNewVar(mgr.cuddmgr))

@inline num_nodes(mgr::CuddMgr, xs::Vector{<:Ptr}; as_add=true) = begin
    as_add && (xs = map(x -> rref(Cudd_BddToAdd(mgr.cuddmgr, x)), xs))
    Cudd_SharingSize(xs, length(xs))
end

@inline num_vars(mgr::CuddMgr, xs::Vector{<:Ptr}) = begin
    Cudd_VectorSupportSize(mgr.cuddmgr, xs, length(xs))
end
        
@inline num_vars(mgr::CuddMgr) =
    Cudd_ReadSize(mgr.cuddmgr)

mutable struct FILE end

@inline dump_dot(mgr::CuddMgr, xs::Vector{<:Ptr}, filename; as_add=true) = begin
    # convert to ADDs in order to properly print terminals
    if as_add
        xs = map(x -> rref(Cudd_BddToAdd(mgr.cuddmgr, x)), xs)
    end
    outfile = ccall(:fopen, Ptr{FILE}, (Cstring, Cstring), filename, "w")
    Cudd_DumpDot(mgr.cuddmgr, length(xs), xs, C_NULL, C_NULL, outfile) 
    @assert ccall(:fclose, Cint, (Ptr{FILE},), outfile) == 0
    nothing
end

# higher-level functionality specific to Cudd

issat(x::DistBool) =
    issat(x.mgr, x.bit)

isvalid(x::DistBool) =
    isvalid(x.mgr, x.bit)

isliteral(x::DistBool) =
    isliteral(x.mgr, x.bit)

isposliteral(x::DistBool) =
    isposliteral(x.mgr, x.bit)

isnegliteral(x::DistBool) =
    isnegliteral(x.mgr, x.bit)

num_nodes(bits::Vector{DistBool}; as_add=true) =  
    num_nodes(bits[1].mgr, map(b -> b.bit, bits); as_add)

num_nodes(x; as_add=true) =  
    num_nodes(bools(x); as_add)

num_flips(bits::Vector{DistBool}) =  
    num_vars(bits[1].mgr, map(b -> b.bit, bits))

num_flips(x) =  
    num_flips(bools(x))

dump_dot(bits::Vector{DistBool}, filename; as_add=true) =
    dump_dot(bits[1].mgr, map(b -> b.bit, bits), filename; as_add)

dump_dot(x, filename; as_add=true) =  
    dump_dot(bools(x), filename; as_add)
