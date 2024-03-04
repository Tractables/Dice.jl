
# Define RBTree
import Dice: param_lists

struct Color <: InductiveType end
function param_lists(::Type{Color})::Vector{Pair{String,Vector{Type}}}
    [
        "Red" => [],
        "Black" => []
    ]
end
DistRed() = construct(Color, "Red",   [])
DistBlack() = construct(Color, "Black",   [])

struct RBTree <: InductiveType end

function param_lists(::Type{RBTree})::Vector{Pair{String,Vector{Type}}}
    [
        "E" => [],
        "T" => [DistI{Color}, DistI{RBTree}, DistInt32, DistInt32, DistI{RBTree}],
    ]
end

DistRBE() = construct(RBTree, "E",   [])
DistRBT(c::DistI{Color}, l::DistI{RBTree}, k::DistInt32, v::DistInt32, r::DistI{RBTree}) =
    construct(RBTree, "T", [c, l, k, v, r])

function tree_size(e::DistI{RBTree})
    match(e, [
        "E" => () -> DistUInt32(0),
        "T" => (c, l, k, v, r) -> DistUInt32(1) + tree_size(l) + tree_size(r),
    ])
end

function is_red(c::DistI{Color})
    match(c, [
        "Red" => () -> true,
        "Black" => () -> false
    ])
end

# Check that all paths through the tree have the same number of black nodes
function satisfies_bookkeeping_invariant(e::DistI{RBTree})
    function black_height_and_valid(t::DistI{RBTree})
        match(t, [
            "E" => () -> (DistUInt32(1), true),
            "T" => (c, l, k, v, r) -> begin
                left_black_height, left_valid = black_height_and_valid(l)
                right_black_height, right_valid = black_height_and_valid(r)
                @dice_ite if left_valid && right_valid && prob_equals(left_black_height, right_black_height) 
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
function satisfied_balance_invariant(e::DistI{RBTree})
    function color_and_valid(t::DistI{RBTree})
        match(t, [
            "E" => () -> (DistBlack(), true),
            "T" => (c, l, k, v, r) -> begin
                left_color, left_valid = color_and_valid(l)
                right_color, right_valid = color_and_valid(r)
                if left_valid && right_valid && !(is_red(c) && (is_red(left_color) || is_red(right_color)))
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

function satisfies_black_root_invariant(t::DistI{RBTree})
    match(t, [
        "E" => () -> true,
        "T" => (c, l, k, v, r) -> !isred(c)
    ])
end
