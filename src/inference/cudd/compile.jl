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

function BDDCompiler()
    c = BDDCompiler(
        initialize_cudd(),
        Set{AnyBool}(),
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
    c
end

# It's okay if not all of these are actually actually roots (i.e. some are
# descendants of others), because including a descendant will not change the set
# of nodes that foreach_node(roots) considers.
#
# It may be problematic to add roots once we've started compiling, though.
# Currently all users of this code add all roots at the start, but if this
# changes, we need to think more about GC.
function BDDCompiler(roots)
    c = BDDCompiler()
    add_roots!(c, roots)
    c
end

function add_roots!(c::BDDCompiler, roots)
    # De-dupe
    roots = unique(setdiff(roots, c.roots))
    union!(c.roots, roots)

    # Collect flips and reference count
    flips = Vector{Flip}()
    foreach_node(roots) do node
        node isa Flip && push!(flips, node)
        for child in unique(children(node))
            get!(c.num_uncompiled_parents, child, 0)
            c.num_uncompiled_parents[child] += 1
        end
    end

    # Compile flips so variable order matches instantiation order, and save
    # levels.
    sort!(flips; by=f -> f.global_id)
    for f in unique(flips)
        haskey(c.cache, f) && continue
        n = new_var(c.mgr)
        c.cache[f] = n
        c.level_to_flip[level(n)] = f
    end    
end

function compile(c::BDDCompiler, root::AnyBool)::CuddNode
    compile(c, [root])[1]
end

function compile(c::BDDCompiler, roots::Vector{<:AnyBool})::Vector{CuddNode}
    # TODO: don't add here; maintain set of covered nodes, panic if not covered
    add_roots!(c, roots)
    [compile_existing(c, root) for root in roots]
end

function compile_existing(c::BDDCompiler, root::AnyBool)::CuddNode
    haskey(c.cache, root) && return c.cache[root]
    root ∉ c.roots && error("Can only compile roots added to BDDCompiler")

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

# Given `context`, a surrounding path condition, and a test
# returns (path condition if test, path condition if !test)
function split(c::BDDCompiler, context::CuddNode, test::AnyBool)::Tuple{CuddNode, CuddNode}
    # TODO: Think about GC
    testbdd = compile(c, test)
    ifbdd = conjoin(c.mgr, context, testbdd)
    if ifbdd === context
        context, constant(c.mgr, false)
    elseif !issat(c.mgr, ifbdd)
        constant(c.mgr, false), context
    else
        nottestbdd = negate(c.mgr, testbdd)
        elsebdd = conjoin(c.mgr, context, nottestbdd)
        ifbdd, elsebdd
    end
end
