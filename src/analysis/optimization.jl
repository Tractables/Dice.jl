using DirectedAcyclicGraphs

#########################
# make canonical computation graph
#########################

"Replace each computation graph node by its canonical representation"
canonicalize(root::Bool, cache = nothing) = root

function canonicalize(root::Dist{Bool})
    cache = Dict{Tuple,Dist{Bool}}()
    canonical_root = canonicalize(root, cache)
    canonical_root, cache
end

function canonicalize(root::Dist{Bool}, cache)
    fl(n::Flip) = n # flips are by definition canonical
    fi(n::Union{DistOr,DistAnd}, call) = begin
        uniquex, uniquey = call(n.x), call(n.y)
        get!(cache, (typeof(n), uniquex, uniquey)) do 
            uniquex === n.x && uniquey === n.y && return n
            uniquen = typeof(n)(uniquex, uniquey)
            @assert  uniquex === uniquen.x && uniquey === uniquen.y 
            uniquen
        end
    end
    fi(n::DistNot, call) = begin
        uniquex = call(n.x)
        get!(cache, (DistNot, uniquex)) do 
            uniquex === n.x && return n
            uniquen = !uniquex
            @assert  uniquex === uniquen.x
            uniquen
        end
    end
    foldup(root, fl, fi, Dist{Bool})
end

#########################
# optimize UNSAT by literal propagation
#########################

"Eliminate IR nodes that are provably false or true using unit propagation"
function optimize_unsat(root)
    y, canonical = canonicalize(root)
    universe = reused_nodes(y)
    _, conditions = unitconditions(y, universe)
    optimize_unsat(y, universe, conditions, canonical);
end

function optimize_unsat(root, universe, conditions, canonicalnodes)
    cache = Dict{Dist{Bool},AnyBool}()
    while true
        root = canonicalize(root, canonicalnodes)
        root_prev = root
        unitconditions(root, universe, conditions)
        root = optimize_unsat_once(root, conditions, cache)
        if root_prev !== root
            @info "One iteration of `optimize_unsat` changed IR size from $(num_ir_nodes(root_prev)) to $(num_ir_nodes(root))"
        end
        root_prev === root && break
    end
    root
end

optimize_unsat_once(root::Bool, conditions, cache) = root

function optimize_unsat_once(root::Dist{Bool}, conditions, cache)
    fl(n) = n # flips are by definition sat/non-tautological
    fi(n, call) = begin
        n_cond = conditions[n]
        if unsat_conditions(n_cond)
            @info  "Optimizing UNSAT IR node away: $n_cond"
            return false
        elseif tautological_conditions(n_cond)
            @info  "Optimizing tautological IR node away: $n_cond"
            return true
        else
            return reconstitute(n, call)
        end
    end
    foldup(root, fl, fi, AnyBool, cache)
end

function reconstitute(n, call::Function)
    newx = call(n.x)
    if n isa DistNot
        reconstitute(n, newx)
    else
        newy = call(n.y)
        reconstitute(n, newx, newy)
    end
end

reconstitute(n::DistNot, newx::AnyBool) = 
    return newx === n.x ? n : !newx

reconstitute(n::DistAnd, newx::AnyBool, newy::AnyBool) = begin
    newx === n.x && newy === n.y && return n
    return newx & newy
end

reconstitute(n::DistOr, newx::AnyBool, newy::AnyBool) = begin
    newx === n.x && newy === n.y && return n
    return newx | newy
end

#########################
# optimize condition by literal propagation
#########################

function optimize_condition(root)
    y, canonical = canonicalize(root);
    universe = reused_nodes(y);
    _, conditions = unitconditions(y, universe);
    _, scopecache = scope(y, universe);
    optimize_condition(y, universe, conditions, scopecache, canonical);
end

function optimize_condition(root, universe, conditions, scopecache, canonicalnodes)
    unsatcache = Dict{Dist{Bool},AnyBool}()
    propcache = Dict{Dist{Bool},AnyBool}()
    while true
        root = canonicalize(root, canonicalnodes)
        root_prevprev = root
        unitconditions(root, universe, conditions)
        scope(root, universe, scopecache)
        root = optimize_unsat_once(root, conditions, unsatcache)
        if root_prevprev !== root           
            root = canonicalize(root, canonicalnodes)
            unitconditions(root, universe, conditions)
            scope(root, universe, scopecache)
            @info "One iteration of `optimize_unsat` changed IR size from $(num_ir_nodes(root_prevprev)) to $(num_ir_nodes(root))"
        end
        root_prev = root
        root = optimize_condition_once(root, conditions, scopecache, propcache)
        if root_prev !== root
            @info "One iteration of `optimize_condition` changed IR size from $(num_ir_nodes(root_prev)) to $(num_ir_nodes(root))"
        end
        root_prevprev === root && break
    end
    root
end

function optimize_condition_once(root, conditions, scope, cache)
    fl(n::Flip) = n # flips are by definition sat
    fi(n, call) = begin
        if n isa DistBoolBinOp
            x_prop, y_prop = propagated_literals(n, conditions, scope)
            if !isempty(x_prop) || !isempty(y_prop)
                @info "Can propagate $(length(x_prop))/$(length(y_prop)) literals between inputs of $n"
                newx = condition(n.x, x_prop, scope)
                newy = condition(n.y, y_prop, scope)
                @assert newx !== n.x || newy !== n.y
                return reconstitute(n, newx, newy)
            end
        end
        return reconstitute(n, call)
    end
    foldup(root, fl, fi, AnyBool, cache)
end

function condition(root, literals, scope)
    fl(n) = begin
        (n,true) ∈ literals && return true
        (n,false) ∈ literals && return false
        return n
    end 
    fi(n, call) = begin
        n_scope = scope[n]
        if any(l -> l[1] ∈ n_scope, literals)
            (n, true) ∈ literals && return true
            (n, false) ∈ literals && return false
            return reconstitute(n, call)
        else
            return n
        end
    end
    foldup(root, fl, fi, AnyBool)
end

