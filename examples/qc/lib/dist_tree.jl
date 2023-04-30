# Define DistTree
import Dice: param_lists

struct DistTree{T} <: DistInductiveType end

function param_lists(::Type{DistTree{T}})::Vector{Pair{String,Vector{Type}}} where T <: Union{Dist, AnyBool}
    [
        "Leaf" => [],
        "Branch" => [T, DistInductive{DistTree{T}}, DistInductive{DistTree{T}}],
    ]
end

DistLeaf(T)          = construct(DistTree{T}, "Leaf",   [])
DistBranch(x::T, l::DistInductive{DistTree{T}}, r::DistInductive{DistTree{T}}) where T =
    construct(DistTree{T}, "Branch", [x, l, r])

function depth(l::DistInductive{DistTree{T}}) where T
    prob_match(l, [
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
