using CUDD
using Dice

# Construct a rather arbitrary BDD and count the number of nodes.
# Params control auto reordering type, and whether we manually dereference
# intermediary BDDs.
function main(reordering_type, deref_intermediaries)
    mgr = CuddMgr(reordering_type)

    fs = [new_var(mgr, 0.5) for _ in 1:60]
    xs = Vector{Any}(undef, 60)
    xs[1] = new_var(mgr, 0.5)
    for i in 2:60
        temp = disjoin(mgr, fs[i], fs[i ÷ 2])
        xs[i] = conjoin(mgr, temp, xs[i - 1])
        deref_intermediaries && Cudd_RecursiveDeref(mgr.cuddmgr, temp)
        deref_intermediaries && Cudd_RecursiveDeref(mgr.cuddmgr, xs[i - 1])
    end
    num_bdd_nodes(mgr, [last(xs)])
end

#== Prints out the table below
CUDD_REORDER_NONE    | default:   196604    with manual derefs:   196604
CUDD_REORDER_SIFT    | default:     4820    with manual derefs:      168
CUDD_REORDER_WINDOW2 | default:   196860    with manual derefs:    45020
==#
for reordering_type in [CUDD.CUDD_REORDER_NONE, CUDD.CUDD_REORDER_SIFT, CUDD.CUDD_REORDER_WINDOW2]
    wo = main(reordering_type, false)
    w = main(reordering_type, true)
    println("$(rpad(reordering_type, 20)) | default: $(lpad(wo, 8))    with manual derefs: $(lpad(w, 8))")
end