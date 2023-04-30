using Revise
using Dice
import Dice: param_lists
# Define DistList

struct DistList{T} <: DistInductive{Any}
    constructor::DistUInt32
    arg_lists::Vector{Union{Vector,Nothing}}
end

function param_lists(::Type{<:DistList{T}})::Vector{Pair{String,Vector{Type}}} where T <: Dist{<:Any} #Union{<:Dist, AnyBool}
    [
        "Nil" => [],
        "Cons" => [T, DistList{T}],
    ]
end

DistNil(T) = construct(DistList{T}, "Nil",  [])
DistCons(x::T, xs::DistList{T}) where T = construct(DistList{T}, "Cons", [x, xs])

function len(l)
    prob_match(l, [
        "Nil"  => ()      -> DistUInt32(0),
        "Cons" => (x, xs) -> DistUInt32(1) + len(xs),
    ])
end
