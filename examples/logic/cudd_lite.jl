using CUDD

struct BDD
    cudd_ptr::Ptr{Nothing}
end

mgr = initialize_cudd()
Cudd_DisableGarbageCollection(mgr)

choice() = BDD(rref(Cudd_bddNewVar(mgr)))
rref(x) = begin 
    ref(x)
    x
end
Base.:(&)(x::BDD, y::BDD) = BDD(rref(Cudd_bddAnd(mgr, x.cudd_ptr, y.cudd_ptr)))
Base.:(|)(x::BDD, y::BDD) = BDD(rref(Cudd_bddOr(mgr, x.cudd_ptr, y.cudd_ptr)))
Base.:(!)(x::BDD) = BDD(rref(Cudd_Not(x.cudd_ptr)))
ite(x::BDD, y::BDD, z::BDD) = BDD(rref(Cudd_bddIte(mgr, x.cudd_ptr, y.cudd_ptr, z.cudd_ptr)))

fal = BDD(Cudd_ReadLogicZero(mgr))
tru = BDD(Cudd_ReadOne(mgr))

dump_dot(x::BDD, filename) = dump_dot([x], filename)

mutable struct FILE end
function dump_dot(xs, filename)
    xs = map(x -> rref(Cudd_BddToAdd(mgr, x.cudd_ptr)), xs)
    outfile = ccall(:fopen, Ptr{FILE}, (Cstring, Cstring), filename, "w")
    Cudd_DumpDot(mgr, length(xs), xs, C_NULL, C_NULL, outfile) 
    @assert ccall(:fclose, Cint, (Ptr{FILE},), outfile) == 0
    nothing
end

nothing

Base.:(^)(x::BDD, y::Bool) = if y !x else x end
eq(x::BDD, y::Bool) = !(x ^ y)