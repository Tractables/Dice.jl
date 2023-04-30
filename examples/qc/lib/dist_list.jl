# Define DistList
import Dice: param_lists

struct DistList{T} <: DistInductiveType end

function param_lists(::Type{DistList{T}})::Vector{Pair{String,Vector{Type}}} where T <: Union{Dist, AnyBool}
    [
        "Nil" => [],
        "Cons" => [T, DistInductive{DistList{T}}],
    ]
end

DistNil(T) = construct(DistList{T}, "Nil",  [])
DistCons(x::T, xs::DistInductive{DistList{T}}) where T =
    construct(DistList{T}, "Cons", [x, xs])

function len(l::DistInductive{DistList{T}}) where T
    prob_match(l, [
        "Nil"  => ()      -> DistUInt32(0),
        "Cons" => (x, xs) -> DistUInt32(1) + len(xs),
    ])
end
