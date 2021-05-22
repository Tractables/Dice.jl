# compilation backend that uses CUDD

using CUDD

struct CuddMgr
    cuddmgr::Ptr{Nothing}
end

function default_manager() 
    cudd_mgr = initialize_cudd()
    Cudd_DisableGarbageCollection(cudd_mgr)
    CuddMgr(cudd_mgr)
end

true_node(mgr::CuddMgr) = 
    Cudd_ReadOne(mgr.cuddmgr)

false_node(mgr::CuddMgr) = 
    Cudd_ReadLogicZero(mgr.cuddmgr)

biconditional(mgr::CuddMgr, x, y) =
    Cudd_bddXnor(mgr.cuddmgr, x, y)

conjoin(mgr::CuddMgr, x, y) =
    Cudd_bddAnd(mgr.cuddmgr, x, y)

disjoin(mgr::CuddMgr, x, y) =
    Cudd_bddOr(mgr.cuddmgr, x, y)

negate(mgr::CuddMgr, x) =
    # workaround until https://github.com/sisl/CUDD.jl/issues/16 is fixed
    biconditional(mgr, x, false_node(mgr))

ite(mgr::CuddMgr, cond, then, elze) =
    Cudd_bddIte(mgr.cuddmgr, cond, then, elze)

issat(mgr::CuddMgr, x) =
    x !== false_node(mgr)

new_var(mgr::CuddMgr) =
    Cudd_bddNewVar(mgr.cuddmgr)

num_nodes(::CuddMgr, xs::Vector{<:Ptr}) = 
    Cudd_SharingSize(xs, length(xs))

num_flips(mgr::CuddMgr) =
    Cudd_ReadSize(mgr.cuddmgr)
