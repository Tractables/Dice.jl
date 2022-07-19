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

function optimize_unsat(root, universe, conditions, canonicalnodes)
    root = canonicalize(root, canonicalnodes)
    cache = Dict{Dist{Bool},AnyBool}()
    while true
        root_prev = root
        unitconditions(root, universe, conditions)
        root = optimize_unsat_once(root, conditions, cache)
        root = canonicalize(root, canonicalnodes)
        if root_prev !== root
            @info "One iteration of `optimize_unsat` reduced IR size from $(num_ir_nodes(root_prev)) to $(num_ir_nodes(root))"
        end
        root_prev === root && break
    end
    root
end

optimize_unsat_once(root::Bool, conditions, cache) = root

function optimize_unsat_once(root::Dist{Bool}, conditions, cache)
    fl(n::Flip) = n # flips are by definition sat
    fi(n, call) = begin
        n_cond = conditions[n]
        if unsat_conditions(n_cond)
            @info  "Optimizing UNSAT IR node away: $n_cond"
            return false
        elseif tautological_conditions(n_cond)
            @info  "Optimizing tautological IR node away: $n_cond"
            return true
        else
            newx = call(n.x)
            if n isa DistNot
                return newx === n.x ? n : !newx
            else
                newy = call(n.y)
                newx === n.x && newy === n.y && return n
                if n isa DistAnd
                    return newx & newy
                else
                    @assert n isa DistOr
                    return newx | newy
                end
            end
        end
    end
    foldup(root, fl, fi, AnyBool, cache)
end

#########################
# optimize condition by literal propagation
#########################

function optimize_condition_once(root, conditions, scope, cache = Dict{Dist{Bool},AnyBool}())
    fl(n::Flip) = n # flips are by definition sat
    fi(n, call) = begin
        if n isa DistNot
            newx = call(n.x)
            return newx === n.x ? n : !newx
        else
            x_prop, y_prop = propagated_literals(n, conditions, scope)
            if !isempty(x_prop)
                @info "Can propagate literals $x_prop from $n to $(n.x)"
                error()
            end
            if !isempty(y_prop)
                @info "Can propagate literals $y_prop from $n to $(n.y)"
                error()
            end
            newx, newy = call(n.x), call(n.y)
            newx === n.x && newy === n.y && return n
            if n isa DistAnd
                return newx & newy
            else
                @assert n isa DistOr
                return newx | newy
            end
        end
    end
    foldup(root, fl, fi, AnyBool, cache)
end

function propagated_literals(n::DistAnd, conditions, scope)
    x_conds = conditions[n.x]
    y_conds = conditions[n.y]
    x_scope = scope[n.x]
    y_scope = scope[n.y]
    # x in (n = x AND y) can be simplified if y |= l and x |/= l but has l in scope
    x_prop = setdiff(x_scope ∩ y_conds.necessary, x_conds.necessary)
    # y in (n = x AND y) can be simplified if x |= l and y |/= l but has l in scope
    y_prop = setdiff(y_scope ∩ x_conds.necessary, y_conds.necessary)
    return x_prop, y_prop
end

function propagated_literals(n::DistOr, conditions, scope)
    x_conds = conditions[n.x]
    y_conds = conditions[n.y]
    x_scope = scope[n.x]
    y_scope = scope[n.y]
    # x in (n = x OR y) can be simplified if -y |= l and -x |/= l but has l in scope
    x_prop = setdiff(x_scope ∩ y_conds.sufficientnot, x_conds.sufficientnot)
    # y in (n = x OR y) can be simplified if x |= l and y |/= l but has l in scope
    y_prop = setdiff(y_scope ∩ x_conds.sufficientnot, y_conds.sufficientnot)
    return x_prop, y_prop
end