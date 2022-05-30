import IfElse: ifelse

export Dist, DistBool, prob_equals, infer_bool, ifelse, flip, bools, dist_to_mgr_and_compiler, flips_left_to_right, flips_by_instantiation_order, flips_by_deepest_depth, flips_by_shallowest_depth, flips_by_freq

"A probability distribution over values of type `T`"
abstract type Dist{T} end

"The global context of a dice program analysis"
abstract type DiceManager end

abstract type DistBool <: Dist{Bool} end

struct DistAnd <: DistBool
    x::DistBool
    y::DistBool
end

struct DistOr <: DistBool
    x::DistBool
    y::DistBool
end

struct DistNot <: DistBool
    x::DistBool
end

struct DistEquals <: DistBool
    x::DistBool
    y::DistBool
end

struct DistIte <: DistBool
    c::DistBool
    t::DistBool
    e::DistBool
end

struct DistTrue <: DistBool end

struct DistFalse <: DistBool end

struct Flip <: DistBool
    id::Int
end

flip_next_id = 1
flip_probs = Dict{Int, AbstractFloat}()
function flip(p::Real)
    if iszero(p)
        return DistFalse()
    elseif isone(p)
        return DistTrue()
    end
    f = Flip(flip_next_id)
    global flip_probs[flip_next_id] = p
    global flip_next_id += 1
    f
end

DistBool(b::Bool) =
    if b DistTrue() else DistFalse() end

DistBool(p::Real) =
    if iszero(p)
        DistFalse()
    elseif isone(p)
        DistTrue()
    else
        flip(p)
    end

# Abuse of method overloading to keep computation graph flat
Base.:&(x::DistFalse, y::DistFalse) = DistFalse()
Base.:&(x::DistFalse, y::DistTrue) = DistFalse()
Base.:&(x::DistTrue, y::DistFalse) = DistFalse()
Base.:&(x::DistTrue, y::DistTrue) = DistTrue()
Base.:&(x::DistFalse, y::DistBool) = DistFalse()
Base.:&(x::DistBool, y::DistFalse) = DistFalse()
Base.:&(x::DistTrue, y::DistBool) = y
Base.:&(x::DistBool, y::DistTrue) = x
Base.:&(x::DistBool, y::DistBool) = DistAnd(x, y)

Base.:&(x::DistBool, y::Bool) = x & DistBool(y)
Base.:&(x::Bool, y::DistBool) = DistBool(x) & y

Base.:|(x::DistFalse, y::DistFalse) = DistFalse()
Base.:|(x::DistFalse, y::DistTrue) = DistTrue()
Base.:|(x::DistTrue, y::DistFalse) = DistTrue()
Base.:|(x::DistTrue, y::DistTrue) = DistTrue()
Base.:|(x::DistFalse, y::DistBool) = y
Base.:|(x::DistBool, y::DistFalse) = x
Base.:|(x::DistTrue, y::DistBool) = DistTrue()
Base.:|(x::DistBool, y::DistTrue) = DistTrue()
Base.:|(x::DistBool, y::DistBool) = DistOr(x, y)

Base.:|(x::DistBool, y::Bool) = x | DistBool(y)
Base.:|(x::Bool, y::DistBool) = DistBool(x) | y

Base.:!(x::DistFalse) = DistTrue()
Base.:!(x::DistTrue) = DistFalse()
Base.:!(x::DistNot) = x.x
Base.:!(x::DistBool) = DistNot(x)

prob_equals(x::DistFalse, y::DistFalse) = DistTrue()
prob_equals(x::DistFalse, y::DistTrue) = DistFalse()
prob_equals(x::DistTrue, y::DistFalse) = DistFalse()
prob_equals(x::DistTrue, y::DistTrue) = DistTrue()
prob_equals(x::DistFalse, y::DistBool) = !y
prob_equals(x::DistBool, y::DistFalse) = !x
prob_equals(x::DistTrue, y::DistBool) = y
prob_equals(x::DistBool, y::DistTrue) = x
prob_equals(x::DistBool, y::DistBool) = DistEquals(x, y)

prob_equals(x::DistBool, y::Bool) = prob_equals(x, DistBool(y))
prob_equals(x::Bool, y::DistBool) = prob_equals(DistBool(x), y)

ifelse(cond::DistFalse, then::DistFalse, elze::DistFalse) = DistFalse()
ifelse(cond::DistFalse, then::DistFalse, elze::DistTrue) = DistTrue()
ifelse(cond::DistFalse, then::DistTrue, elze::DistFalse) = DistFalse()
ifelse(cond::DistFalse, then::DistTrue, elze::DistTrue) = DistTrue()

ifelse(cond::DistTrue, then::DistFalse, elze::DistFalse) = DistFalse()
ifelse(cond::DistTrue, then::DistFalse, elze::DistTrue) = DistFalse()
ifelse(cond::DistTrue, then::DistTrue, elze::DistFalse) = DistTrue()
ifelse(cond::DistTrue, then::DistTrue, elze::DistTrue) = DistTrue()

ifelse(cond::DistTrue, then::DistBool, elze::DistBool) = then
ifelse(cond::DistFalse, then::DistBool, elze::DistBool) = elze
ifelse(cond::DistBool, then::DistFalse, elze::DistFalse) = DistFalse()
ifelse(cond::DistBool, then::DistTrue, elze::DistFalse) = cond
ifelse(cond::DistBool, then::DistFalse, elze::DistTrue) = !cond
ifelse(cond::DistBool, then::DistTrue, elze::DistTrue) = DistTrue()

ifelse(cond::DistBool, then::DistBool, elze::DistBool) = DistIte(cond, then, elze)
ifelse(cond::DistBool, x::Bool, y::DistBool) = ifelse(cond, DistBool(x), y)
ifelse(cond::DistBool, x::DistBool, y::Bool) = ifelse(cond, x, DistBool(y))
ifelse(cond::DistBool, x::Bool, y::Bool) = ifelse(cond, DistBool(x), DistBool(y))

ifelse(cond::DistBool, then::Tuple, elze::Tuple) = tuple([ifelse(cond, t, e) for (t, e) in zip(then, elze)]...)

bools(b::DistBool) = [b]

struct FlipTree
    flip_or_children::Union{Flip, Vector{FlipTree}}
end

FlipTree(x::DistAnd) = FlipTree(Vector{FlipTree}([FlipTree(x.x), FlipTree(x.y)]))
FlipTree(x::DistOr) = FlipTree(Vector{FlipTree}([FlipTree(x.x), FlipTree(x.y)]))
# Choose to have NOT not add depth because they are cheap for BDDs, worth experimenting though
FlipTree(x::DistNot) = FlipTree(x.x)
FlipTree(x::DistEquals) = FlipTree(Vector{FlipTree}([FlipTree(x.x), FlipTree(x.y)]))
FlipTree(x::DistIte) = FlipTree(Vector{FlipTree}([FlipTree(x.c), FlipTree(x.t), FlipTree(x.e)]))
FlipTree(x::DistTrue) = FlipTree(Vector{FlipTree}())
FlipTree(x::DistFalse) = FlipTree(Vector{FlipTree}())
FlipTree(x::AbstractVector{T}) where T <: DistBool = FlipTree(Vector{FlipTree}([FlipTree(y) for y in x]))

function flips_left_to_right(x::FlipTree)::Vector{Int}
    flip_ids = Vector{Int}()
    flips_left_to_right_helper(x, flip_ids)
    unique(flip_ids)
end

function flips_left_to_right_helper(x::FlipTree, flip_ids::Vector{Int})
    if x.flip_or_children isa Flip
        push!(flip_ids, x.flip_or_children.id)
    else
        for child in x.flip_or_children
            flips_left_to_right_helper(child, flip_ids)
        end
    end
end

function flips_by_instantiation_order(x::FlipTree)::Vector{Int}
    sort(flips_left_to_right(x))
end

function flips_by_freq(x::FlipTree)::Vector{Int}
    flip_id_ctr = Dict{Int, Int}()
    flips_by_freq_helper(x, flip_id_ctr)
    [kv[1] for kv in sort(collect(flip_id_ctr), by=kv->(kv[2], -kv[1]))]
end

function flips_by_freq_helper(x::FlipTree, flip_id_ctr::Dict{Int, Int})
    if x.flip_or_children isa Flip
        flip_id_ctr[x.flip_or_children.id] = get(flip_id_ctr, x.flip_or_children.id, 0) + 1
    else
        for child in x.flip_or_children
            flips_by_freq_helper(child, flip_id_ctr)
        end
    end
end

function flips_by_deepest_depth(x::FlipTree)::Vector{Int}
    flip_id_to_depth = Dict{Int, Int}()
    flips_by_deepest_depth_helper(x, 0, flip_id_to_depth)
    [kv[1] for kv in sort(collect(flip_id_to_depth), by=kv->kv[2])]
end

function flips_by_deepest_depth_helper(x::FlipTree, depth::Int, flip_id_to_depth::Dict{Int, Int})
    if x.flip_or_children isa Flip
        if !haskey(flip_id_to_depth, x.flip_or_children.id) || depth > flip_id_to_depth[x.flip_or_children.id]
            flip_id_to_depth[x.flip_or_children.id] = depth
        end
    else
        for child in x.flip_or_children
            flips_by_deepest_depth_helper(child, depth + 1, flip_id_to_depth)
        end
    end
end

function flips_by_shallowest_depth(x::FlipTree)::Vector{Int}
    flip_id_to_depth = Dict{Int, Int}()
    flips_by_shallowest_depth_helper(x, 0, flip_id_to_depth)
    [kv[1] for kv in sort(collect(flip_id_to_depth), by=kv->kv[2])]
end

function flips_by_shallowest_depth_helper(x::FlipTree, depth::Int, flip_id_to_depth::Dict{Int, Int})
    if x.flip_or_children isa Flip
        if !haskey(flip_id_to_depth, x.flip_or_children.id) || depth < flip_id_to_depth[x.flip_or_children.id]
            flip_id_to_depth[x.flip_or_children.id] = depth
        end
    else
        for child in x.flip_or_children
            flips_by_shallowest_depth_helper(child, depth + 1, flip_id_to_depth)
        end
    end
end

# Lock in the flip order for a dist
# Returns mgr and function to compile computation graph to BDD
function dist_to_mgr_and_compiler(x; flip_order=nothing, flip_order_reverse=false)
    if flip_order === nothing
        flip_order = flips_by_instantiation_order
    end
    flips_ordered = flip_order(FlipTree(bools(x)))
    if flip_order_reverse
        reverse!(flips_ordered)
    end
    
    mgr = CuddMgr()
    flip_vars = Dict()
    for flip_id in flips_ordered
        flip_vars[flip_id] = new_var(mgr, flip_probs[flip_id])
    end

    # to_bdd(x::DistAnd) = conjoin(mgr, to_bdd(x.x), to_bdd(x.y))
    # to_bdd(x::DistOr) = disjoin(mgr, to_bdd(x.x), to_bdd(x.y))
    # to_bdd(x::DistNot) = negate(mgr, to_bdd(x.x))
    # to_bdd(x::DistEquals) = biconditional(mgr, to_bdd(x.x), to_bdd(x.y))
    # to_bdd(x::DistIte) = ite(mgr, to_bdd(x.c), to_bdd(x.t), to_bdd(x.e))
    # to_bdd(x::DistTrue) = constant(mgr, true)
    # to_bdd(x::DistFalse) = constant(mgr, false)
    # to_bdd(x::Flip) = flip_vars[x.id]
    # return mgr, to_bdd

    # TODO: do we need to memoize?
    cache = Dict{UInt64, Ptr{Nothing}}()
    function to_bdd_mem(x)
        oid = objectid(x)
        if !haskey(cache, oid)
            cache[oid] = to_bdd(x)
        end
        cache[oid]
    end
    to_bdd(x::DistAnd) = conjoin(mgr, to_bdd_mem(x.x), to_bdd_mem(x.y))
    to_bdd(x::DistOr) = disjoin(mgr, to_bdd_mem(x.x), to_bdd_mem(x.y))
    to_bdd(x::DistNot) = negate(mgr, to_bdd_mem(x.x))
    to_bdd(x::DistEquals) = biconditional(mgr, to_bdd_mem(x.x), to_bdd_mem(x.y))
    to_bdd(x::DistIte) = ite(mgr, to_bdd_mem(x.c), to_bdd_mem(x.t), to_bdd_mem(x.e))
    to_bdd(x::DistTrue) = constant(mgr, true)
    to_bdd(x::DistFalse) = constant(mgr, false)
    to_bdd(x::Flip) = flip_vars[x.id]
    return mgr, to_bdd_mem
end

function infer_bool(d::DistBool)
    mgr, to_bdd = dist_to_mgr_and_compiler(d)
    infer_bool(mgr, to_bdd(d))
end