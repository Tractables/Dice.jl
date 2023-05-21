# Treat dict as a vector, not necessarily indexed by natural numbers

DictVec = AbstractDict{<:Any, <:Real}

add_dicts(x::DictVec, y::DictVec) =
    Dict(
        k => get(x, k, 0) + get(y, k, 0)
        for k in union(keys(x), keys(y))
    )

sub_dicts(x::DictVec, y::DictVec) =
    Dict(
        k => get(x, k, 0) - get(y, k, 0)
        for k in union(keys(x), keys(y))
    )

scale_dict(c::Real, x::DictVec) =
    Dict(k => c * v for (k, v) in x)
