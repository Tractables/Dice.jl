# Define DistTree

DistTree = InductiveDistType()
DistTree.constructors = [
    ("Leaf",  []),
    ("Branch", [Dist, DistTree, DistTree]),
]

DistLeaf()          = construct(DistTree, "Leaf",   ())
DistBranch(x, l, r) = construct(DistTree, "Branch", (x, l, r))

function depth(l)
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
