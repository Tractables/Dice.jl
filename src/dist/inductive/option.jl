
export Opt, DistNone, DistSome

struct Opt{T} <: InductiveType end
function param_lists(::Type{Opt{T}})::Vector{Pair{String,Vector{Type}}} where T
    [
        "None" => [],
        "Some" => [T],
    ]
end

DistNone(T) = construct(Opt{T}, "None",  [])
DistSome(x::T) where T = construct(Opt{T}, "Some", [x])
