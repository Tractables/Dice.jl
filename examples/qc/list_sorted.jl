using Dice

hi = 8

# returns (list, evidence)
function genList(size, lo=DistUInt32(0))
    if size == 0
        return (DistVector{DistUInt32}(), true)
    end

    @dice_ite if flip(0.5)
        (DistVector{DistUInt32}(), true)
    else
        x = uniform(DistUInt32, 0, hi)
        list, evid = genList(size-1, x)
        prob_append(list, x), (x >= lo) & evid
    end
end

println("started")
list, evid = @time genList(3)
debug_info_ref = Ref{CuddDebugInfo}()
d = @time pr(list, evidence=evid, algo=Cudd(debug_info_ref=debug_info_ref))
println(d)
println(debug_info_ref[].num_nodes)

# 104 -> 72 nodes
# hi = 8
# size = 3