# compilation backend that uses CUDD
export get_cudd_mgr, dice_init, infer_bool, num_vars, num_flips
using CUDD

cudd_mgr = Ptr{Nothing}()
probs = Dict{Int,Float64}()
initialized = Ref(false)
function dice_init()
    if initialized[]
        return
    end
    initialized[] = true
    global cudd_mgr = initialize_cudd()
    Cudd_DisableGarbageCollection(cudd_mgr) # note: still need to ref because CUDD can delete nodes without doing a GC pass
end

function get_cudd_mgr()
    dice_init()
    return cudd_mgr
end

##################################
# core functionality
##################################

function constant(c:: Bool) 
    c ? Cudd_ReadOne(get_cudd_mgr()) : Cudd_ReadLogicZero(get_cudd_mgr())
end

biconditional(x, y) =
    rref(Cudd_bddXnor(get_cudd_mgr(), x, y))

conjoin(x, y) =
    rref(Cudd_bddAnd(get_cudd_mgr(), x, y))

disjoin(x, y) =
    rref(Cudd_bddOr(get_cudd_mgr(), x, y))

negate(x) = 
    Cudd_Not(x)

ite(cond, then, elze) =
    rref(Cudd_bddIte(get_cudd_mgr(), cond, then, elze))

new_var(prob) = begin
    x = rref(Cudd_bddNewVar(get_cudd_mgr()))
    probs[decisionvar(x)] = prob
    x
end

function infer_bool(x)
    dice_init()
    cache = Dict{Tuple{Ptr{Nothing},Bool},Float64}()
    t = constant(true)
    cache[(t,false)] = log(one(Float64))
    cache[(t,true)] = log(zero(Float64))
    
    rec(y, c) = 
        if Cudd_IsComplement(y)
            rec(Cudd_Regular(y), !c)   
        else get!(cache, (y,c)) do 
                v = decisionvar(y)
                prob = probs[v]
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

##################################
# additional CUDD-based functionality
##################################

function Base.show(io::IO, x::Ptr{Nothing}) 
    if !issat(x)
        print(io, "(false)") 
    elseif isvalid(x)
        print(io, "(true)")
    elseif isposliteral(x)
        print(io, "(f$(decisionvar(x)))")
    elseif isnegliteral(x)
        print(io, "(-f$(decisionvar(x)))")
    else    
        print(io, "@$(hash(x)÷ 10000000000000)")
    end
end

isconstant(x) =
    isone(Cudd_IsConstant(x))

isliteral(x) =
    (!isconstant(x) &&
     isconstant(Cudd_T(x)) &&
     isconstant(Cudd_E(x)))

isposliteral(x) =
    isliteral(x) && 
    (x === Cudd_bddIthVar(cudd_mgr, decisionvar(x)))

isnegliteral(x) =
    isliteral(x) && 
    (x !== Cudd_bddIthVar(cudd_mgr, decisionvar(x)))

issat(x) =
    x !== constant(false)

isvalid(x) =
    x === constant(true)

num_nodes(xs::Vector{<:Ptr}; as_add=true) = begin
    as_add && (xs = map(x -> rref(Cudd_BddToAdd(get_cudd_mgr(), x)), xs))
    Cudd_SharingSize(xs, length(xs))
end

num_flips(x) =  
    num_flips(bools(x))

num_vars(xs::Vector{<:Ptr}) = begin
    Cudd_VectorSupportSize(get_cudd_mgr(), xs, length(xs))
end
        
num_vars() =
    Cudd_ReadSize(get_cudd_mgr())


decisionvar(x) =
    Cudd_NodeReadIndex(x)

dump_dot(x, filename; as_add=true) =  
    dump_dot(bools(x), filename; as_add)

mutable struct FILE end

dump_dot(xs::Vector{<:Ptr}, filename; as_add=true) = begin
    # convert to ADDs in order to properly print terminals
    if as_add
        xs = map(x -> rref(Cudd_BddToAdd(get_cudd_mgr(), x)), xs)
    end
    outfile = ccall(:fopen, Ptr{FILE}, (Cstring, Cstring), filename, "w")
    Cudd_DumpDot(get_cudd_mgr(), length(xs), xs, C_NULL, C_NULL, outfile) 
    @assert ccall(:fclose, Cint, (Ptr{FILE},), outfile) == 0
    nothing
end

##################################
# CUDD Utilities
##################################

rref(x) = begin 
    ref(x)
    x
end