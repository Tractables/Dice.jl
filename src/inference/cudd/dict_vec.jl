# Treat dict as a vector, not necessarily indexed by natural numbers

DictVec = AbstractDict{<:Any, <:AbstractFloat}

Base.:(+)(x::DictVec, y::DictVec) =
    Dict(
        k => get(x, k, 0.) + get(y, k, 0.)
        for k in union(keys(x), keys(y))
    )

Base.:(-)(x::DictVec, y::DictVec) =
    Dict(
        k => get(x, k, 0.) - get(y, k, 0.)
        for k in union(keys(x), keys(y))
    )

Base.:(*)(c::AbstractFloat, x::DictVec) =
    Dict(k => c * v for (k, v) in x)
