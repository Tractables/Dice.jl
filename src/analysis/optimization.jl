#########################
# make canonical computation graph
#########################

"Replace each computation graph node by its canonical representation"
function canonicalize(root::Dist{Bool})
    cache = Dict{Tuple,Dist{Bool}}()
    canonical_root = canonicalize(root, cache)
    canonical_root, cache
end

function canonicalize(root::Dist{Bool}, cache)
    fl(n::Flip) = n # flips are by definition canonical
    fi(n::Union{DistOr,DistAnd}, call) = begin
        uniquex, uniquey = call(n.x), call(n.y)
        get!(cache, (typeof(n), uniquex, uniquey)) do 
            uniquex === n.x && uniquey === n.y && return n
            uniquen = typeof(n)(uniquex, uniquey)
            @assert  uniquex === uniquen.x && uniquey === uniquen.y 
            uniquen
        end
    end
    fi(n::DistNot, call) = begin
        uniquex = call(n.x)
        get!(cache, (DistNot, uniquex)) do 
            uniquex === n.x && return n
            uniquen = !uniquex
            @assert  uniquex === uniquen.x
            uniquen
        end
    end
    foldup(root, fl, fi, Dist{Bool})
end

#########################
# optimize necessary and sufficient literal conditions
#########################

function optimize_unsat(root, conditions)
    fl(n::Flip) = n # flips are by definition sat
    fi(n, call) = begin
        n_cond = conditions[n]
        if unsat_conditions(n_cond)
            println("optimizing UNSAT node away: $n_cond")
            return false
        elseif tautological_conditions(n_cond)
            println("optimizing tautological node away: $n_cond")
            return true
        else
            newx = call(n.x)
            if n isa DistNot
                return newx === n.x ? n : !newx
            else
                newy = call(n.y)
                newx === n.x && newy === n.y && return n
                if n isa DistAnd
                    return newx & newy
                else
                    @assert n isa DistOr
                    return newx | newy
                end
            end
        end
    end
    foldup(root, fl, fi, AnyBool)
end