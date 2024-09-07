# Define Tree
module KVTree
    using Dice
    using Main: Nat
    @inductive t E() T(t, Nat.t, Nat.t, t)
end
type_to_coq(::Type{KVTree.t}) = "Tree"

bst_ctor_to_id = Dict(
    :E => DistInt32(0),
    :T => DistInt32(1),
)

function ctor_to_id(ctor::KVTree.t)
    match(ctor, [
        :E => () -> bst_ctor_to_id[:E]
        :T => (_, _, _, _) -> bst_ctor_to_id[:T]
    ])
end

function satisfies_order_invariant(t::KVTree.t)
    function helper(t, lo, hi)
        @match t [
            E() -> true,
            T(l, k, v, r) -> begin
                (if isnothing(lo) true else lo < k end) &
                (if isnothing(hi) true else k < hi end) &
                helper(l, lo, k) &
                helper(r, k, hi)
            end
        ]
    end
    helper(t, nothing, nothing)
end

function eq_except_numbers(x::KVTree.t, y::KVTree.t)
    @match x [
        E() -> (@match y [
            E() -> true,
            T(yl, yk, yv, yr) -> false,
        ]),
        T(xl, xk, xv, xr) -> (@match y [
            E() -> false,
            T(yl, yk, yv, yr) -> eq_except_numbers(xl, yl) & eq_except_numbers(xr, yr),
        ]),
    ]
end

function tree_size(e::KVTree.t)
    match(e, [
        :E => () -> DistUInt32(0),
        :T => (l, k, v, r) -> DistUInt32(1) + tree_size(l) + tree_size(r),
    ])
end

function depth(e::KVTree.t)
    @match e [
        E() -> DistUInt32(0),
        T(l, k, v, r) -> DistUInt32(1) + max(depth(l), depth(r))
    ]
end
