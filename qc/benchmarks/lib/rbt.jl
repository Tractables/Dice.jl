
# Define RBTree
using Dice

module Color
    using Dice
    @inductive t R() B()
end
function Base.string(c::Color.t)
    @assert isdeterministic(c)
    @match c [
        R() -> "Color.R()",
        B() -> "Color.B()",
    ]
end
type_to_coq(::Type{Color.t}) = "Color"

module ColorKVTree
    using Dice
    using Main: Z, Color
    @inductive t E() T(Color.t, t, Z.t, Z.t, t)
end
type_to_coq(::Type{ColorKVTree.t}) = "Tree"

function tree_size(e::ColorKVTree.t)
    @match e [
        E() -> DistUInt32(0),
        T(c, l, k, v, r) -> DistUInt32(1) + tree_size(l) + tree_size(r),
    ]
end

function depth(e::ColorKVTree.t)
    @match e [
        E() -> DistUInt32(0),
        T(c, l, k, v, r) -> begin
            ldepth = depth(l)
            rdepth = depth(r)
            DistUInt32(1) + @alea_ite if ldepth > rdepth ldepth else rdepth end
        end
    ]
end

is_red(c::Color.t) = matches(c, :R)

# Check that all paths through the tree have the same number of black nodes
function satisfies_bookkeeping_invariant(e::ColorKVTree.t)
    function black_height_and_valid(t::ColorKVTree.t)
        @match t [
            E() -> (DistUInt32(1), true),
            T(c, l, k, v, r) -> begin
                left_black_height, left_valid = black_height_and_valid(l)
                right_black_height, right_valid = black_height_and_valid(r)
                @alea_ite if left_valid & right_valid & prob_equals(left_black_height, right_black_height) 
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
function satisfies_balance_invariant(e::ColorKVTree.t)
    function color_and_valid(t::ColorKVTree.t)
        @match t [
            E() -> (Color.B(), true),
            T(c, l, k, v, r) -> begin
                left_color, left_valid = color_and_valid(l)
                right_color, right_valid = color_and_valid(r)
                @alea_ite if left_valid & right_valid & !(is_red(c) & (is_red(left_color) | is_red(right_color)))
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

function satisfies_black_root_invariant(t::ColorKVTree.t)
    @match t [
        E() -> true,
        T(c, l, k, v, r) -> !is_red(c)
    ]
end

function satisfies_order_invariant(t::ColorKVTree.t)
    function helper(t, lo, hi)
        @match t [
            E() -> true,
            T(c, l, k, v, r) -> begin
                (if isnothing(lo) true else lo < k end) &
                (if isnothing(hi) true else k < hi end) &
                helper(l, lo, k) &
                helper(r, k, hi)
            end
        ]
    end
    helper(t, nothing, nothing)
end

function eq_except_numbers(x::ColorKVTree.t, y::ColorKVTree.t)
    @match x [
        E() -> (@match y [
            E() -> true,
            T(yc, yl, yk, yv, yr) -> false,
        ]),
        T(xc, xl, xk, xv, xr) -> (@match y [
            E() -> false,
            T(yc, yl, yk, yv, yr) -> prob_equals(xc, yc) & eq_except_numbers(xl, yl) & eq_except_numbers(xr, yr),
        ]),
    ]
end
