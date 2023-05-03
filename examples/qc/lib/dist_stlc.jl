# Define DistSTLC

DistTyp = InductiveDistType()
DistTyp.constructors = [
    ("TBool", []),
    ("TFun",  [DistTyp, DistTyp]),
]

DistExpr = InductiveDistType()
DistExpr.constructors = [
    ("Var",     [DistUInt32]),
    ("Boolean", [AnyBool]),
    ("Abs",     [DistTyp, DistExpr]),
    ("App",     [DistExpr, DistExpr])
]

DistTBool()        = construct(DistTyp, "TBool", ())
DistTFun(fty, xty) = construct(DistTyp, "TFun",  (fty, xty))

DistVar(i)     = construct(DistExpr, "Var",     (i,))
DistBoolean(b) = construct(DistExpr, "Boolean", (b,))
DistAbs(ty, e) = construct(DistExpr, "Abs",     (ty, e))
DistApp(f, x)  = construct(DistExpr, "App",     (f, x))

# DistBind = InductiveDistType()
# DistBind.constructors = [
#     ("BindNow"
# ]


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
