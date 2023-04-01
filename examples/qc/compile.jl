# Contain ugly CUDD stuff/interaction with Dice compilation here.

# Returns a pair:
#   1. bdds_to_maximize: CUDD BDD nodes we want to maximize likelihood of
#   2. flip_to_group: map flip to corresponding group
mgr = nothing
ccache = nothing
function compile_helper(bools_to_maximize::Vector{<:AnyBool}, flip_to_group)
    bools_to_maximize = [x for x in bools_to_maximize if x isa Dist{Bool}]
    debug_info_ref = Ref{CuddDebugInfo}()
    pr(vcat(bools_to_maximize, collect(keys(flip_to_group)))..., algo=Cudd(debug_info_ref=debug_info_ref))

    # Keep manager in scope so Cudd_Quit doesn't get called
    global mgr = debug_info_ref[].mgr
    global ccache = debug_info_ref[].ccache

    bdds_to_maximize = [ccache[b] for b in bools_to_maximize]
    level_to_group = Dict(
        level(ccache[f]) => group
        for (f, group) in flip_to_group
    )
    bdds_to_maximize, level_to_group
end
