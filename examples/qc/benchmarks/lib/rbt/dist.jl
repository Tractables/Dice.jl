
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
