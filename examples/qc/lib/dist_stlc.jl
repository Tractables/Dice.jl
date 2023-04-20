# Define DistSTLC

DistSTLCType = InductiveDistType()
DistSTLCType.constructors = [
    ("Arrow",   [DistSTLCType, DistSTLCType]),
    ("TypeVar", [DistString]),
]

DistSTLC = InductiveDistType()
DistSTLC.constructors = [
    ("Var", [DistString]),
    ("App", [DistSTLC, DistSTLC]),
    ("Abs", [DistString, DistSTLCType, DistSTLC]),
]

DistArrow(arg_ty, ret_ty) = construct(DistSTLCType, "Arrow", (arg_ty, ret_ty))
DistTypeVar(s)            = construct(DistSTLCType, "TypeVar", (s,))

DistVar(s)        = construct(DistSTLC, "Var", (s,))
DistApp(e1, e2)   = construct(DistSTLC, "App", (e1, e2))
DistAbs(s, ty, e) = construct(DistSTLC, "Abs", (s, ty, e))

function ast_depth(l)
    prob_match(l, [
        "Var"    => ()      -> DistUInt32(0),
        "App"    => (e1, e2) -> begin
            d1, d2 = depth(e1), depth(e2)
            @dice_ite if d1 > d2
                DistUInt32(1) + d1
            else
                DistUInt32(1) + d2
            end
        end,
        "Abs"    => (s, ty, e) -> DistUInt32(1) + depth(e),
    ])
end
