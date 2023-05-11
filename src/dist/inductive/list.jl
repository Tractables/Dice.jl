# Define List
export List, DistNil, DistCons, prob_append, concat

struct List{T} <: InductiveType end

function param_lists(::Type{List{T}})::Vector{Pair{String,Vector{Type}}} where T <: Union{Dist, AnyBool}
    [
        "Nil" => [],
        "Cons" => [T, DistI{List{T}}],
    ]
end

DistNil(T) = construct(List{T}, "Nil",  [])
DistCons(x::T, xs::DistI{List{T}}) where T =
    construct(List{T}, "Cons", [x, xs])

function Base.length(l::DistI{List{T}}) where T
    match(l, [
        "Nil"  => ()      -> DistUInt32(0),
        "Cons" => (x, xs) -> DistUInt32(1) + length(xs),
    ])
end

function rev_concat(l::DistI{List{T}}, acc::DistI{List{T}}) where T
    match(l, [
        "Nil"  => ()      -> acc,
        "Cons" => (x, xs) -> rev_concat(xs, DistCons(x, acc)),
    ]) 
end

function Base.reverse(l::DistI{List{T}}) where T
    rev_concat(l, DistNil(T))
end

function concat(l1::DistI{List{T}}, l2::DistI{List{T}}) where T
    rev_concat(reverse(l1), l2)
end

function prob_append(l::DistI{List{T}}, x::T) where T
    concat(l, DistCons(x, DistNil(T)))
end
