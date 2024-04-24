
# Define RBTree
using Dice

module Color
    using Dice
    @inductive T Red() Black()
end

module ColorKVTree
    using Dice
    using Main: DistNat, Color
    @inductive T Leaf() Node(Color.T, T, DistInt32, DistInt32, T)
end

function tree_size(e::ColorKVTree.T)
    @match e [
        Leaf() -> DistUInt32(0),
        Node(c, l, k, v, r) -> DistUInt32(1) + tree_size(l) + tree_size(r),
    ]
end

is_red(c::Color.T) = matches(c, :Red)

# Check that all paths through the tree have the same number of black nodes
function satisfies_bookkeeping_invariant(e::ColorKVTree.T)
    function black_height_and_valid(t::ColorKVTree.T)
        @match t [
            Leaf() -> (DistUInt32(1), true),
            Node(c, l, k, v, r) -> begin
                left_black_height, left_valid = black_height_and_valid(l)
                right_black_height, right_valid = black_height_and_valid(r)
                @dice_ite if left_valid & right_valid & prob_equals(left_black_height, right_black_height) 
                    left_black_height + if is_red(c) DistUInt32(0) else DistUInt32(1) end, true
                else
                    DistUInt32(0), false
                end
            end,
        ]
    end
    _black_height, valid = black_height_and_valid(e)
    valid
end

# Check that all red nodes have black children
function satisfies_balance_invariant(e::ColorKVTree.T)
    function color_and_valid(t::ColorKVTree.T)
        @match t [
            Leaf() -> (Color.Black(), true),
            Node(c, l, k, v, r) -> begin
                left_color, left_valid = color_and_valid(l)
                right_color, right_valid = color_and_valid(r)
                @dice_ite if left_valid & right_valid & !(is_red(c) & (is_red(left_color) | is_red(right_color)))
                    c, true
                else
                    c, false
                end
            end,
        ]
    end
    _color, valid = color_and_valid(e)
    valid
end

function satisfies_black_root_invariant(t::ColorKVTree.T)
    @match t [
        Leaf() -> true,
        Node(c, l, k, v, r) -> !is_red(c)
    ]
end

function satisfies_order_invariant(t::ColorKVTree.T)
    function helper(t, lo, hi)
        @match t [
            Leaf() -> true,
            Node(c, l, k, v, r) -> begin
                (if isnothing(lo) true else lo < k end) &
                (if isnothing(hi) true else k < hi end) &
                helper(l, lo, k) &
                helper(r, k, hi)
            end
        ]
    end
    helper(t, nothing, nothing)
end

function eq_except_numbers(x::ColorKVTree.T, y::ColorKVTree.T)
    @match x [
        Leaf() -> (@match y [
            Leaf() -> true,
            Node(yc, yl, yk, yv, yr) -> false,
        ]),
        Node(xc, xl, xk, xv, xr) -> (@match y [
            Leaf() -> false,
            Node(yc, yl, yk, yv, yr) -> prob_equals(xc, yc) & eq_except_numbers(xl, yl) & eq_except_numbers(xr, yr),
        ]),
    ]
end
