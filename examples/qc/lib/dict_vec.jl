# Treat dict as a vector, not necessarily indexed by natural numbers

Base.:(+)(x::Dict, y::Dict) =
    Dict(k => x[k] + y[k] for k in keys(x))

Base.:(-)(x::Dict, y::Dict) =
    Dict(k => x[k] - y[k] for k in keys(x))

Base.:(*)(c::Number, x::Dict) =
    Dict(k => c * v for (k, v) in x)

function Base.clamp!(x::Dict, lo, hi)
    for (k, v) in x
        x[k] = clamp(v, lo, hi)
    end
end
