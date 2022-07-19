
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

"necessary and sufficient literal conditions (implied literals)"
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

unsat_conditions(x) = 
    isempty(x.sufficientnot) && any(l -> negate(l) ∈ x.necessary, x.necessary)

tautological_conditions(x) = 
    isempty(x.necessary) && any(l -> negate(l) ∈ x.sufficientnot, x.sufficientnot)

Base.show(io::IO, x::UnitConditions) = 
    print(io, "UnitConditions: $(x.necessary...) vs. $(x.sufficientnot...)")

"Compute the necessary and sufficient literal conditions (implied literals)"
function unitconditions(root::Dist{Bool}, universe)
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

include("optimization.jl")