
num_ir_nodes(x::Bool) = 0
num_ir_nodes(x::Dist{Bool}) = 
    DirectedAcyclicGraphs.num_nodes(x)

#########################
# compute scope of computation graph
#########################

"Compute the set of reused computation graph nodes"
function reused_nodes(root::Dist{Bool})
    np = num_parents(root)
    mp = filter!(kv -> kv[2] > 1, np)
    # let negation nodes be represented by their non-negated node
    nonneg = map(collect(keys(mp))) do n 
        n isa DistNot ? n.x : n
    end
    Set(nonneg)
end

const Scope = Set{Dist{Bool}}

"Compute the scope of the computation graph"
function scope(root::Dist{Bool}, universe)
    cache = Dict{Dist{Bool},Scope}()
    scope_root = scope(root, universe, cache)
    scope_root, cache
end

function scope(root::Dist{Bool}, universe, cache)
    fl(n::Flip) = (n ∈ universe) ? Scope([n]) : Scope() 
    fi(n::Union{DistOr,DistAnd}, call) = begin
        s = call(n.x) ∪ call(n.y)
        (n ∈ universe) ? push!(s, n) : s
    end
    fi(n::DistNot, call) = begin
        s = call(n.x)
        (n ∈ universe) ? push!(s, n) : s
    end
    foldup(root, fl, fi, Scope, cache)
end

#########################
# analyze necessary and sufficient literal conditions (implied literals)
#########################

const Literal = Tuple{Dist{Bool}, Bool}

"Necessary and sufficient literal conditions (implied literals)"
struct UnitConditions
    # set of implied literals
    necessary::Set{Literal}
    # set of implied literals of the formula's negation
    sufficientnot::Set{Literal}
end

UnitConditions() = 
    UnitConditions(Set{Literal}(), Set{Literal}())

UnitConditions(n::Dist{Bool}) = 
    UnitConditions(Set{Literal}([(n, true)]), 
                   Set{Literal}([(n, false)]))

function Base.push!(x::UnitConditions, n::Dist{Bool}) 
    push!(x.necessary, (n,true))
    push!(x.sufficientnot, (n,false))
    x
end

conjoin_conditions(x, y) = UnitConditions(
    x.necessary ∪ y.necessary,
    x.sufficientnot ∩ y.sufficientnot)

disjoin_conditions(x, y) = UnitConditions(
    x.necessary ∩ y.necessary,
    x.sufficientnot ∪ y.sufficientnot)

negate_conditions(x) = UnitConditions(
    x.sufficientnot, x.necessary)

negate(l::Literal)::Literal = (l[1], !l[2])

"are there two literal conditions that imply the formula is UNSAT"
unsat_conditions(x) = 
    any(l -> negate(l) ∈ x.necessary, x.necessary)

"are there two literal conditions that imply the formula is tautological"
tautological_conditions(x) = 
    any(l -> negate(l) ∈ x.sufficientnot, x.sufficientnot)

""
equiv_conditions(x, n) = 
    [l for l in x.necessary if l[1]!=n && negate(l) ∈ x.sufficientnot]

tautcond_conditions(x) = 
    x.necessary ∩ x.sufficientnot

Base.show(io::IO, x::UnitConditions) = 
    print(io, "UnitConditions: $(length(x.necessary))/$(length(x.sufficientnot))")

"Compute the necessary and sufficient literal conditions (implied literals)"
function unitconditions(root::Dist{Bool}, universe = reused_nodes(root))
    cache = Dict{Dist{Bool},UnitConditions}()
    cond_root = unitconditions(root, universe, cache)
    cond_root, cache
end

unitconditions(root::Bool, universe, cache) = nothing

function unitconditions(root::Dist{Bool}, universe, cache)
    fl(n::Flip) = 
        (n ∈ universe) ? UnitConditions(n) : UnitConditions()
    fi(n::DistAnd, call) = begin
        c = conjoin_conditions(call(n.x), call(n.y))
        (n ∈ universe) ? push!(c, n) : c
    end
    fi(n::DistOr, call) = begin
        c = disjoin_conditions(call(n.x), call(n.y))
        (n ∈ universe) ? push!(c, n) : c
    end
    fi(n::DistNot, call) = begin
        c = negate_conditions(call(n.x))
        (n ∈ universe) ? push!(c, n) : c
    end
    foldup(root, fl, fi, UnitConditions, cache)
end

#########################
# analyze unit propagation
#########################

function propagated_literals(n::DistAnd, conditions, scope)
    x_conds = conditions[n.x]
    y_conds = conditions[n.y]
    x_scope = scope[n.x]
    y_scope = scope[n.y]
    # x in (n = x AND y) can be simplified if y |= l and x |/= l but has l in scope
    x_prop = filter(l -> l[1] ∈ x_scope && l ∉ x_conds.necessary, y_conds.necessary)
    # y in (n = x AND y) can be simplified if x |= l and y |/= l but has l in scope
    y_prop = filter(l -> l[1] ∈ y_scope && l ∉ y_conds.necessary, x_conds.necessary)
    return x_prop, y_prop
end

function propagated_literals(n::DistOr, conditions, scope)
    x_conds = conditions[n.x]
    y_conds = conditions[n.y]
    x_scope = scope[n.x]
    y_scope = scope[n.y]
    # x in (n = x OR y) can be simplified if -y |= l and -x |/= l but has l in scope
    x_prop = filter(l -> l[1] ∈ x_scope && l ∉ x_conds.sufficientnot, y_conds.sufficientnot)
    # y in (n = x OR y) can be simplified if x |= l and y |/= l but has l in scope
    y_prop = filter(l -> l[1] ∈ y_scope && l ∉ y_conds.sufficientnot, x_conds.sufficientnot)
    return x_prop, y_prop
end

include("optimization.jl")