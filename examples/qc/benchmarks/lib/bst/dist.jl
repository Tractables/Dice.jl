# Define Tree
module KVTree
    using Dice
    using Main: DistNat
    @inductive T Leaf() Node(T, DistNat, DistNat, T)
end

bst_ctor_to_id = Dict(
    :Leaf => DistInt32(0),
    :Node => DistInt32(1),
)

function ctor_to_id(ctor::KVTree.T)
    match(ctor, [
        :Leaf => () -> bst_ctor_to_id[:Leaf]
        :Node => (_, _, _, _) -> bst_ctor_to_id[:Node]
    ])
end

function satisfies_order_invariant(t::KVTree.T)
    function helper(t, lo, hi)
        @match t [
            Leaf() -> true,
            Node(l, k, v, r) -> begin
                (if isnothing(lo) true else lo < k end) &
                (if isnothing(hi) true else k < hi end) &
                helper(l, lo, k) &
                helper(r, k, hi)
            end
        ]
    end
    helper(t, nothing, nothing)
end

function eq_except_numbers(x::KVTree.T, y::KVTree.T)
    @match x [
        Leaf() -> (@match y [
            Leaf() -> true,
            Node(yl, yk, yv, yr) -> false,
        ]),
        Node(xl, xk, xv, xr) -> (@match y [
            Leaf() -> false,
            Node(yl, yk, yv, yr) -> eq_except_numbers(xl, yl) & eq_except_numbers(xr, yr),
        ]),
    ]
end
