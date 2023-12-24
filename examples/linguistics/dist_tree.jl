# Define Tree
import Dice: param_lists

struct Tree{T} <: InductiveType end

function param_lists(::Type{Tree{T}})::Vector{Pair{String,Vector{Type}}} where T <: Union{Dist, AnyBool}
    [
        "Leaf" => [T],
        "Branch" => [T, DistVector],
    ]
end

DistLeaf(x::T) where T = construct(Tree{T}, "Leaf", [x])
DistBranch(x::T, children::DistVector) where T =
    construct(Tree{T}, "Branch", [x, children])

function leaves(t)
    match(t, [
        "Leaf"    => (x)      -> DistVector([x]),
        "Branch"  => (x, children) -> begin
            res = DistVector{DistEnum}()
            for i in 1:Dice.maxvalue(children.len)
                res = ifelse(DistUInt32(i) <= children.len,
                    prob_extend(res, leaves(prob_getindex(children, DistUInt32(i)))),
                    res)
            end
            res
        end
    ])
end

function prob_append_child(t, child)
    match(t, [
        "Leaf"   => (_) -> error("cant append to leaf"),
        "Branch" => (x, children) -> begin
            DistBranch(x, prob_append(children, child))
        end
    ])
end