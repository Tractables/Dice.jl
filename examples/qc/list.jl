using Dice

function genList(size)
    if prob_equals(size, DistUInt32(0))
        return DistVector{DistUInt32}()
    end
    
    if flip(0.5)
        return DistVector{DistUInt32}()
    end
    return prob_extend(genList(size - DistUInt32(1)), DistVector{DistUInt32}([DistUInt32(5)]))
end
#==
version above, for size 2
4.040133 seconds (9.53 M allocations: 492.850 MiB, 7.58% gc time, 98.75% compilation time)
DataStructures.DefaultDict{Any, Any, Float64}([5, 5] => 0.25, Int64[] => 0.5, [5] => 0.25)
==#



function genList(size)
    res = DistVector{DistUInt32}()
    for i = 1:size
        res = ifelse(flip(0.5), prob_extend(res, DistVector{DistUInt32}([DistUInt32(5)])), DistVector{DistUInt32}())
    end
    res
end

println("started")
md = @time genList(1000)
debug_info_ref = Ref{CuddDebugInfo}()
d = @time pr(md, algo=Cudd(debug_info_ref=debug_info_ref))
# println(d)
println(debug_info_ref[].num_nodes)

