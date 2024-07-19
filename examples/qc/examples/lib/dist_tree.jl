# Define Tree
import Dice: param_lists

struct Tree{T} <: InductiveType end

function param_lists(::Type{Tree{T}})::Vector{Pair{String,Vector{Type}}} where T <: Union{Dist, AnyBool}
    [
        "Leaf" => [],
        "Branch" => [T, Tree{T}, Tree{T}],
    ]
end

DistLeaf(T)          = construct(Tree{T}, "Leaf",   [])
DistBranch(x::T, l::Tree{T}, r::Tree{T}) where T =
    construct(Tree{T}, "Branch", [x, l, r])

function depth(l::Tree{T}) where T
    match(l, [
        "Leaf"    => ()      -> DistUInt32(0),
        "Branch"  => (x, l, r) -> begin
            dl, dr = depth(l), depth(r)
            @dice_ite if dl > dr
                DistUInt32(1) + dl
            else
                DistUInt32(1) + dr
            end
        end
    ])
end
