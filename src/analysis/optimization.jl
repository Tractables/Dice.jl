using DirectedAcyclicGraphs

include("computationgraphs.jl")

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

# Compress flip ids so that multiple Alea programs run in the same Julia program
# still have consistent canonicalizations.
#
# For example, let some program produce flips {0, 1, 2}. When run again, it will
# produce flips {3, 4, 5}.
#
# This func creates {0->0, 1->1, 2->2} for the first run and {3->0, 4->1, 5->2}
# for the second, so canonicalize sees {0, 1, 2} for both.
function compress_flip_ids(root::Dist{Bool})
    ids = Set()

    function fl(n::Flip)
        push!(ids, n.global_id)
        n
    end

    function fi(n, call)
        for child in children(n)
            call(child)
        end
        n
    end

    foldup(root, fl, fi, Dist{Bool})

    ids = collect(ids)
    sort!(ids)
    return Dict((id, idx) for (idx, id) in enumerate(ids))
end


function canonicalize(root::Dist{Bool}, cache)
    flip_id_compression = compress_flip_ids(root)
    deterministic_hash_cache = Dict()
    function deterministic_hash(n)
        if isa(n, Flip)
            return flip_id_compression[n.global_id]
        end

        if !haskey(deterministic_hash_cache, n)
            children_hashes = collect(map(deterministic_hash, children(n)))
            deterministic_hash_cache[n] = hash(children_hashes)
        end

        return deterministic_hash_cache[n]
    end

    fl(n::Flip) = n # flips are by definition canonical
    fi(n::Union{DistOr,DistAnd}, call) = begin
        uniquex, uniquey = call(n.x), call(n.y)
        if deterministic_hash(uniquex) > deterministic_hash(uniquey)
            uniquex, uniquey = uniquey, uniquex
        end
        get!(cache, (typeof(n), uniquex, uniquey)) do 
            uniquex === n.x && uniquey === n.y && return n
            uniquen = typeof(n)(uniquex, uniquey)
            @assert uniquex === uniquen.x && uniquey === uniquen.y
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
    canonical_root = foldup(root, fl, fi, Dist{Bool})
    # if canonical_root !== root
    #     @info "One iteration of `canonicalize` changed IR size from $(num_ir_nodes(root)) to $(num_ir_nodes(canonical_root))"
    # end
    canonical_root
end

#########################
# optimize UNSAT/validity by literal propagation
#########################

"Eliminate IR nodes that are provably false or true using unit propagation"
function optimize_unsat(root)
    y, canonical = canonicalize(root)
    universe = reused_nodes(y)
    _, conditions = unitconditions(y, universe)
    optimize_unsat(y, universe, conditions, canonical);
end

function optimize_unsat(root, universe, allconditions, canonicalnodes)
    cache = Dict{Dist{Bool},AnyBool}()
    root = canonicalize(root, canonicalnodes)
    while true
        root_prev = root
        unitconditions(root, universe, allconditions)
        root = optimize_unsat_once(root, allconditions, cache)
        root = canonicalize(root, canonicalnodes)
        if root_prev !== root
            @info "One iteration of `optimize_unsat` changed IR size from $(num_ir_nodes(root_prev)) to $(num_ir_nodes(root))"
        else
            break
        end
    end
    root
end

optimize_unsat_once(root::Bool, conditions, cache) = root

function optimize_unsat_once(root::Dist{Bool}, conditions, cache)
    fl(n) = n # flips are by definition sat/non-tautological
    fi(n, call) = begin
        n_cond = conditions[n]
        if unsat_conditions(n_cond)
            # @info  "Optimizing UNSAT IR node away: $n_cond"
            return false
        elseif tautological_conditions(n_cond)
            # @info  "Optimizing tautological IR node away: $n_cond"
            return true
        else 
            if !(n isa DistNot)
                eqcond = equiv_conditions(n_cond, n)
                if !isempty(eqcond)
                    @assert length(eqcond) == 1
                    lit = first(eqcond)
                    return lit[2] ? lit[1] : !lit[1]
                end
            end
            @assert isempty(tautcond_conditions(n_cond)) "This should never be possible? 99% sure"
            return reconstitute(n, call)
        end
    end
    foldup(root, fl, fi, AnyBool, cache)
end

#########################
# optimize global sufficient and necessary literal conditions
#########################

function optimize_condition_global(root)
    root, canonical = canonicalize(root);
    while root isa Dist
        prev_root = root
        universe = reused_nodes(root)
        _, conditions = unitconditions(root, universe)
        root = optimize_condition_global(root, universe, conditions, canonical)
        (root == prev_root) && break
    end
    root
end

function optimize_condition_global(root, universe, allconditions, canonicalnodes)
    root = optimize_unsat(root, universe, allconditions, canonicalnodes)
    done = Set{Literal}()
    while root isa Dist
        root_prev = root
        conditions = unitconditions(root, universe, allconditions)
        nec = setdiff(conditions.necessary, done)
        sufn = setdiff(conditions.sufficientnot, done)
        if !isempty(nec) || !isempty(sufn)
            state = nec ∪ sufn
            done = done ∪ state
            condcache = Dict{AnyBool,AnyBool}()
            literalnode(literal) = begin
                litnode_cond = condition_children(literal[1], state; cache = condcache)
                literal[2] ? litnode_cond : !litnode_cond
            end
            necnode = mapreduce(literalnode, &, nec; init = true)
            sufnnode = mapreduce(literalnode, &, sufn; init = true)

            core = condition(root, state; cache = condcache)
            root = (core & necnode) | !sufnnode

            @info "One iteration of `optimize_condition_global` on $(length(nec))+$(length(sufn)) literals changed IR size from $(num_ir_nodes(root_prev)) to $(num_ir_nodes(root))"

            root = optimize_unsat(root, universe, allconditions, canonicalnodes)
        else
            break
        end
    end
    root
end

#########################
# EXPERIMENTAL
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
                newn = reconstitute(n, newx, newy)
                @info "Size changed from $(num_ir_nodes(n)) to $(num_ir_nodes(newn))"
                # if num_ir_nodes(newn) < 0.50*num_ir_nodes(n) 
                    return newn
                # else
                #     return n
                # end
            else
                # experiment
                # x_conds = conditions[n.x]
                # y_conds = conditions[n.y]
                # decisions = filter(l -> negate(l) ∈ y_conds.necessary, x_conds.necessary)
                # dualdecisions = filter(l -> negate(l) ∈ y_conds.sufficientnot, x_conds.sufficientnot)
                # if n isa DistAnd && !isempty(dualdecisions)
                #     @info "at least one AND node"
                #     # newx = condition(n.x, Set([decisions[1]]), scope)
                #     # newy = condition(n.y, negate(decisions[2]), scope)
                #     # @assert newx !== n.x || newy !== n.y
                #     # newn = reconstitute(n, newx, newy)
                # elseif n isa DistOr && !isempty(decisions)
                #     @info "deterministic OR node"
                #     # newx = condition(n.x, Set([decisions[1]]), scope)
                #     # newy = condition(n.y, negate(decisions[2]), scope)
                #     # @assert newx !== n.x || newy !== n.y
                #     # newn = reconstitute(n, newx, newy)
                # end
                # is it ever useful to simplify these?
            end
        end
        return reconstitute(n, call)
    end
    foldup(root, fl, fi, AnyBool, cache)
end

function split_and_bound(root)
    best = root
    bestsize = num_ir_nodes(best)
    rootsize = bestsize
    while true
        np = num_parents(root)
        decision, count = sort!(collect(np); by=kv->kv[2], rev=true)[1]
        count <= 2 && break
        @show decision, count
        root_prev = root
        size_prev = rootsize
        t = condition(root, Set([(decision, true)]))
        f = condition(root, Set([(decision, false)]))
        root = (t & decision) | (f & !decision)
        @info "One iteration of `split_and_bound` changed IR size from $(size_prev) to $(num_ir_nodes(root))"
        root = optimize_condition_global(root)
        rootsize = num_ir_nodes(root)
        if rootsize < bestsize
            best, bestsize = root, rootsize
        end
        rootsize > size_prev && break
    end
    best
end