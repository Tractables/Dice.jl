#########################
# compute scope of computation graph
#########################

"Compute the set of reused computation graph nodes"
reused_nodes(root::Dist{Bool}) =
    keys(filter!(kv -> kv[2] > 1, num_parents(root)))

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

"necessary and sufficient literal conditions (implied literals)"
struct UnitConditions
    # set of positive implied literals
    truepos::Scope
    # set of negative implied literals
    trueneg::Scope
    # set of positive implied literals of the formula's negation
    falsepos::Scope
    # set of negative implied literals of the formula's negation
    falseneg::Scope
end

UnitConditions() = 
    UnitConditions(Scope(),Scope(),Scope(),Scope())

UnitConditions(n::Dist{Bool}) = 
    UnitConditions(Scope([n]),Scope(),Scope(),Scope([n]))

function Base.push!(x::UnitConditions, n::Dist{Bool}) 
    push!(x.truepos, n)
    push!(x.falseneg, n)
    x
end

conjoin_conditions(x, y) = UnitConditions(
    x.truepos ∪ y.truepos,
    x.trueneg ∪ y.trueneg,
    x.falsepos ∩ y.falsepos,
    x.falseneg ∩ y.falseneg)

disjoin_conditions(x, y) = UnitConditions(
    x.truepos ∩ y.truepos,
    x.trueneg ∩ y.trueneg,
    x.falsepos ∪ y.falsepos,
    x.falseneg ∪ y.falseneg)

negate_conditions(x) = UnitConditions(
    x.falsepos, x.falseneg, x.truepos, x.trueneg)

unsat_conditions(x) = 
    isempty(x.falsepos) && isempty(x.falseneg) && any(l -> l ∈ x.trueneg, x.truepos)

tautological_conditions(x) = 
    isempty(x.truepos) && isempty(x.trueneg) && any(l -> l ∈ x.falseneg, x.falsepos)

Base.show(io::IO, x::UnitConditions) = 
    print(io, "UnitConditions: $(length(x.truepos))/$(length(x.trueneg))/$(length(x.falsepos))/$(length(x.falseneg))")

"Compute the necessary and sufficient literal conditions (implied literals)"
function unitconditions(root::Dist{Bool}, universe)
    cache = Dict{Dist{Bool},UnitConditions}()
    cond_root = unitconditions(root, universe, cache)
    cond_root, cache
end

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