##################################
# CUDD Compilation
##################################

export BDDCompiler, compile, enable_reordering

mutable struct BDDCompiler
    mgr::CuddMgr
    roots::Set{AnyBool}
    num_uncompiled_parents::Dict{Dist{Bool}, Int}
    cache::Dict{AnyBool, CuddNode}
    level_to_flip::Dict{Integer, Flip}
end

function BDDCompiler(roots)
    c = BDDCompiler(
        initialize_cudd(),
        Set{AnyBool}(roots),
        Dict{Dist{Bool}, Int}(),
        Dict{AnyBool, CuddNode}(),
        Dict{Integer, Any}(),
    )
    Cudd_DisableGarbageCollection(c.mgr)
    c.cache[false] = constant(c.mgr, false)
    c.cache[true] = constant(c.mgr, true)
    finalizer(c) do x
        Cudd_Quit(x.mgr)
    end

    # Collect flips and reference count
    flips = Vector{Flip}()
    foreach_node(c.roots) do node
        node isa Flip && push!(flips, node)
        for child in unique(children(node))
            get!(c.num_uncompiled_parents, child, 0)
            c.num_uncompiled_parents[child] += 1
        end
    end

    # Compile flips so variable order matches instantiation order, and save
    # levels.
    sort!(flips; by=f -> f.global_id)
    for f in flips
        n = new_var(c.mgr)
        c.cache[f] = n
        c.level_to_flip[level(n)] = f
    end

    c
end

function compile(c::BDDCompiler, root::AnyBool)::CuddNode
    haskey(c.cache, root) && return c.cache[root]
    root ∉ c.roots && error("Can only compile roots passed into BDDCompiler")

    # TODO implement shortcuts for equivalence, etc.
    function mark_as_compiled(node)
        for child in unique(children(node))
            c.num_uncompiled_parents[child] -= 1
            @assert c.num_uncompiled_parents[child] >= 0
            if c.num_uncompiled_parents[child] == 0
                Cudd_RecursiveDeref(c.mgr, c.cache[child])
            end
        end
    end
    
    fl(n::Flip) = begin
        if !haskey(c.cache, n)
            error("flip not precompiled")
            # c.cache[n] = new_var(c.mgr)
        end
        c.cache[n]
    end

    fi(n::DistAnd, call) = begin
        if !haskey(c.cache, n)
            call(n.x)
            call(n.y)
            c.cache[n] = conjoin(c.mgr, c.cache[n.x], c.cache[n.y])
            mark_as_compiled(n)
        end
        c.cache[n]
    end

    fi(n::DistOr, call) = begin
        if !haskey(c.cache, n)
            call(n.x)
            call(n.y)
            c.cache[n] = disjoin(c.mgr, c.cache[n.x], c.cache[n.y])
            mark_as_compiled(n)
        end
        c.cache[n]
    end

    # TODO: is GC right with complement arcs? I think so... - Ryan
    fi(n::DistNot, call) = begin
        if !haskey(c.cache, n)
            call(n.x)
            c.cache[n] = negate(c.mgr, c.cache[n.x])
            mark_as_compiled(n)
        end
        c.cache[n]
    end

    foldup(root, fl, fi, CuddNode)
end

function enable_reordering(c::BDDCompiler, reordering_type::CUDD.Cudd_ReorderingType)
    if reordering_type != CUDD.CUDD_REORDER_NONE
        Cudd_AutodynEnable(c.mgr, reordering_type)
    end
end

