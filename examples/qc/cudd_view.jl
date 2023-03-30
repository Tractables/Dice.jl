# CUDD wrappers for viewing BDDs that encapsulate complementation
# - Users of these functions can pretend complement arcs don't exist
# - Avoid "Cudd_" functions outside of this file (mainly Cudd_T and Cudd_E)

using CUDD


# See this PR: https://github.com/sisl/CUDD.jl/pull/24

Fixed_Cudd_Not(node) =
    convert(Ptr{Nothing}, xor(convert(UInt,node), one(UInt)))

Fixed_Cudd_IsComplement(node) =
    isone(convert(UInt,node) & one(UInt))

Fixed_Cudd_Regular(node) =
    convert(Ptr{Nothing}, convert(UInt,node) & ~one(UInt))

CuddNode = CUDD.DdNodePtr

is_constant(x::CuddNode) = isone(Cudd_IsConstant(x))

not(x::CuddNode) = Fixed_Cudd_Not(x)

function high(x::CuddNode)
    @assert !is_constant(x)
    if Fixed_Cudd_IsComplement(x)
        not(Cudd_T(x))
    else
        Cudd_T(x)
    end
end

function low(x::CuddNode)
    @assert !is_constant(x)
    if Fixed_Cudd_IsComplement(x)
        not(Cudd_E(x))
    else
        Cudd_E(x)
    end
end

level(x::CuddNode) = Cudd_NodeReadIndex(x)

# Get a node's manager's one terminal without the manager
function get_one(x::CuddNode)
    x = Fixed_Cudd_Regular(x)
    while !is_constant(x)
        x = Cudd_T(x)
    end
    Fixed_Cudd_Regular(x)
end

function level_traversal(f, root::CuddNode)
    level_to_nodes = []
    function see(x)
        is_constant(x) && return
        i = level(x) + 1  # add 1 to one-index, ensure always a valid index
        while length(level_to_nodes) < i
            push!(level_to_nodes, Set())
        end
        push!(level_to_nodes[i], x)
    end

    see(root)
    cur_level = 1
    while cur_level <= length(level_to_nodes)
        for node in level_to_nodes[cur_level]
            f(node)
            see(low(node))
            see(high(node))
        end
        cur_level += 1
    end
end
