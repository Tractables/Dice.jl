
#########################
# helper functions for rewriting the computation graph
#########################

reconstitute(n::Flip, _::Function) = n

function reconstitute(n, call::Function)
    newx = call(n.x)
    if n isa DistNot
        reconstitute(n, newx)
    else
        newy = call(n.y)
        reconstitute(n, newx, newy)
    end
end

reconstitute(n::DistNot, newx::AnyBool) = 
    return newx === n.x ? n : !newx

reconstitute(n::DistAnd, newx::AnyBool, newy::AnyBool) = begin
    newx === n.x && newy === n.y && return n
    return newx & newy
end

reconstitute(n::DistOr, newx::AnyBool, newy::AnyBool) = begin
    newx === n.x && newy === n.y && return n
    return newx | newy
end

function condition(root, literals, scope=nothing; cache = Dict{AnyBool,AnyBool}())
    isempty(literals) && return root
    fl(n) = begin
        (n,true) ∈ literals && return true
        (n,false) ∈ literals && return false
        return n
    end 
    fi(n, call) = begin
        unaffected = (scope !== nothing) && (
            n_scope = scope[n];
            all(l -> l[1] ∉ n_scope, literals))
        if unaffected
            return n
        else
            (n, true) ∈ literals && return true
            (n, false) ∈ literals && return false
            return reconstitute(n, call)
        end
    end
    foldup(root, fl, fi, AnyBool, cache)
end

condition_children(root, literals, scope=nothing; cache) =
    reconstitute(root, c -> condition(c, literals, scope; cache))
