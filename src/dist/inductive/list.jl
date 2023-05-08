# Define DistList
export DistList, DistNil, DistCons, prob_append, concat

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

function Base.length(l::DistInductive{DistList{T}}) where T
    prob_match(l, [
        "Nil"  => ()      -> DistUInt32(0),
        "Cons" => (x, xs) -> DistUInt32(1) + length(xs),
    ])
end

function rev_concat(l::DistInductive{DistList{T}}, acc::DistInductive{DistList{T}}) where T
    prob_match(l, [
        "Nil"  => ()      -> acc,
        "Cons" => (x, xs) -> rev_concat(xs, DistCons(x, acc)),
    ]) 
end

function Base.reverse(l::DistInductive{DistList{T}}) where T
    rev_concat(l, DistNil(T))
end

function concat(l1::DistInductive{DistList{T}}, l2::DistInductive{DistList{T}}) where T
    rev_concat(reverse(l1), l2)
end

function prob_append(l::DistInductive{DistList{T}}, x::T) where T
    concat(l, DistCons(x, DistNil(T)))
end
