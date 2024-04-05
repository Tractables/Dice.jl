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
