# Contain ugly CUDD stuff/interaction with Dice compilation here.

# Arguments:
#   cond_bools_to_maximize
#      pairs of (bool we want to maximize the likelihood of. BDD of the obs.)
#   flip_to_group:
#      flip to identifier of group of flips that must share their probability
# Returns a pair:
#   1. bdds_to_maximize: pairs of (BDD of nodes we want to maximize likelihood,
#      conjoined with the observation, BDD of observation)
#   2. level_to_group: map BDD level to corresponding group
mgr = nothing
ccache = nothing
function compile_helper(cond_bools_to_maximize::Vector{<:Tuple{<:AnyBool, <:AnyBool}}, flip_to_group)
    cond_bools_to_maximize = [
        ((b & obs), obs)
        for (b, obs) in cond_bools_to_maximize
    ]

    must_compile = Dist{Bool}[]
    for b in Iterators.flatten(cond_bools_to_maximize)
        b isa Dist{Bool} && push!(must_compile, b)
    end
    for flip in keys(flip_to_group)
        push!(must_compile, flip)
    end
    debug_info_ref = Ref{CuddDebugInfo}()
    pr(must_compile, algo=Cudd(debug_info_ref=debug_info_ref))

    # Keep manager in scope so Cudd_Quit doesn't get called
    global mgr = debug_info_ref[].mgr
    global ccache = debug_info_ref[].ccache

    bdds_to_maximize = [(ccache[b], ccache[obs]) for (b, obs) in cond_bools_to_maximize]
    level_to_group = Dict(
        level(ccache[f]) => group
        for (f, group) in flip_to_group
    )
    bdds_to_maximize, level_to_group
end

function compile_helper(bools_to_maximize::Vector{<:AnyBool}, flip_to_group)
    compile_helper([(b, true) for b in bools_to_maximize], flip_to_group)
end