
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
    match(e, [
        :E => () -> DistUInt32(0),
        :T => (c, l, k, v, r) -> DistUInt32(1) + tree_size(l) + tree_size(r),
    ])
end

is_red(c::Color.T) = matches(c, :Red)

# Check that all paths through the tree have the same number of black nodes
function satisfies_bookkeeping_invariant(e::ColorKVTree.T)
    function black_height_and_valid(t::ColorKVTree.T)
        match(t, [
            :E => () -> (DistUInt32(1), true),
            :T => (c, l, k, v, r) -> begin
                left_black_height, left_valid = black_height_and_valid(l)
                right_black_height, right_valid = black_height_and_valid(r)
                @dice_ite if left_valid & right_valid & prob_equals(left_black_height, right_black_height) 
                    left_black_height + if is_red(c) DistUInt32(0) else DistUInt32(1) end, true
                else
                    DistUInt32(0), false
                end
            end,
        ])
    end
    _black_height, valid = black_height_and_valid(e)
    valid
end

# Check that all red nodes have black children
function satisfies_balance_invariant(e::ColorKVTree.T)
    function color_and_valid(t::ColorKVTree.T)
        match(t, [
            :E => () -> (Black(), true),
            :T => (c, l, k, v, r) -> begin
                left_color, left_valid = color_and_valid(l)
                right_color, right_valid = color_and_valid(r)
                @dice_ite if left_valid & right_valid & !(is_red(c) & (is_red(left_color) | is_red(right_color)))
                    c, true
                else
                    c, false
                end
            end,
        ])
    end
    _color, valid = color_and_valid(e)
    valid
end

function satisfies_black_root_invariant(t::ColorKVTree.T)
    match(t, [
        :E => () -> true,
        :T => (c, l, k, v, r) -> !is_red(c)
    ])
end
