# Define DistList

DistList = InductiveDistType()
DistList.constructors = [
    ("Nil",  []),
    ("Cons", [Dist, DistList]),
]

DistNil()       = construct(DistList, "Nil",  ())
DistCons(x, xs) = construct(DistList, "Cons", (x, xs))

function len(l)
    prob_match(l, [
        "Nil"  => ()      -> DistUInt32(0),
        "Cons" => (x, xs) -> DistUInt32(1) + len(xs),
    ])
end
