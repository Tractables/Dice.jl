using DirectedAcyclicGraphs: foldup

function sample(x::Cond{T}) where T
    while true
        vcache = Dict()
        fl(n::Dice.Flip) = begin
            if !haskey(vcache, n)
                prob = if haskey(flip_to_group, n)
                    sigmoid(group_to_psp[flip_to_group[n]])
                else
                    n.prob
                end
                vcache[n] = rand() < prob
            end
            vcache[n]
        end

        fi(n::Dice.DistAnd, call) = begin
            if !haskey(vcache, n)
                vcache[n] = call(n.x) && call(n.y)
            end
            vcache[n]
        end

        fi(n::Dice.DistOr, call) = begin
            if !haskey(vcache, n)
                vcache[n] = call(n.x) || call(n.y)
            end
            vcache[n]
        end

        fi(n::Dice.DistNot, call) = begin
            if !haskey(vcache, n)
                vcache[n] = !call(n.x)
            end
            vcache[n]
        end

        vcache = Dict()
        foldup(x.evid, fl, fi, Bool) || continue
        for bit in tobits(x.x)
            foldup(bit, fl, fi, Bool)
        end
        return frombits(x.x, vcache)
    end
end