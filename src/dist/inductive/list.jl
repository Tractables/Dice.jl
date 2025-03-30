# Define List
export List, Nil, Cons, prob_append, concat, one_of

@type List{T} = Nil() | Cons(T, List{T})

function Base.length(l::List{T}) where T
    match(l, [
        :Nil  => ()      -> DistUInt32(0),
        :Cons => (x, xs) -> DistUInt32(1) + length(xs),
    ])
end

function rev_concat(l::List{T}, acc::List{T}) where T
    match(l, [
        :Nil  => ()      -> acc,
        :Cons => (x, xs) -> rev_concat(xs, Cons(T, x, acc)),
    ]) 
end

function Base.reverse(l::List{T}) where T
    rev_concat(l, Nil(T))
end

function concat(l1::List{T}, l2::List{T}) where T
    rev_concat(reverse(l1), l2)
end

function prob_append(l::List{T}, x::T) where T
    concat(l, Cons(T, x, Nil(T)))
end

function one_of(l::List{T})::Opt.T{T} where T <: Dist
    match(l, [
        :Nil => () -> Opt.None(T),
        :Cons => (x, xs) -> @dice_ite if flip_reciprocal(length(l))
            Opt.Some(T, x)
        else
            one_of(xs)
        end
    ])
end
