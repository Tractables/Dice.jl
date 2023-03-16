using Dice

function genList(size)
    if size == 0
        return DistVector{DistUInt32}()
    end

    return ifelse(
        flip(0.5),
        prob_extend(
            genList(size-1),
            DistVector{DistUInt32}([DistUInt32(5)])
        ),
        DistVector{DistUInt32}()
    )
end

println("started")
md = @time genList(1000)
debug_info_ref = Ref{CuddDebugInfo}()
d = @time pr(md, algo=Cudd(debug_info_ref=debug_info_ref))
# println(d)
println(debug_info_ref[].num_nodes)

