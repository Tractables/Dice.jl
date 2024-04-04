# Define List
export List, Nil, Cons, prob_append, concat, one_of

@inductive List{T} Nil() Cons(T, DistI{List{T}})

function Base.length(l::DistI{List{T}}) where T
    match(l, [
        "Nil"  => ()      -> DistUInt32(0),
        "Cons" => (x, xs) -> DistUInt32(1) + length(xs),
    ])
end

function rev_concat(l::DistI{List{T}}, acc::DistI{List{T}}) where T
    match(l, [
        "Nil"  => ()      -> acc,
        "Cons" => (x, xs) -> rev_concat(xs, Cons(T, x, acc)),
    ]) 
end

function Base.reverse(l::DistI{List{T}}) where T
    rev_concat(l, Nil(T))
end

function concat(l1::DistI{List{T}}, l2::DistI{List{T}}) where T
    rev_concat(reverse(l1), l2)
end

function prob_append(l::DistI{List{T}}, x::T) where T
    concat(l, Cons(T, x, Nil(T)))
end

function one_of(l::DistI{List{T}})::DistI{Opt{T}} where T <: Dist
    match(l, [
        "Nil" => () -> DistNone(T),
        "Cons" => (x, xs) -> @dice_ite if flip_reciprocal(length(l))
            DistSome(x)
        else
            one_of(xs)
        end
    ])
end
