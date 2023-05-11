
export DistOpt, DistNone, DistSome

struct DistOpt{T} <: InductiveType end
function param_lists(::Type{DistOpt{T}})::Vector{Pair{String,Vector{Type}}} where T
    [
        "None" => [],
        "Some" => [T],
    ]
end

DistNone(T) = construct(DistOpt{T}, "None",  [])
DistSome(x::T) where T = construct(DistOpt{T}, "Some", [x])
