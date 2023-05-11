# Define DistSTLC
import Dice: param_lists

struct DistType <: DistInductiveType end
function param_lists(::Type{DistType})
    [
        "TBool" => [],
        "TFun"  => [DistInductive{DistTyp}, DistInductive{DistTyp}],
    ]
end

struct DistExpr <: DistInductiveType end
function param_lists(::Type{DistExpr})
    [
        "Var"     => [DistUInt32],
        "Boolean" => [AnyBool],
        "Abs"     => [DistInductive{DistTyp}, DistInductive{DistExpr}],
        "App"     => [DistInductive{DistExpr}, DistInductive{DistExpr}]
    ]
end

DistTBool()        = construct(DistTyp, "TBool", [])
DistTFun(fty, xty) = construct(DistTyp, "TFun",  [fty, xty])

DistVar(i)     = construct(DistExpr, "Var",     [i])
DistBoolean(b) = construct(DistExpr, "Boolean", [b])
DistAbs(ty, e) = construct(DistExpr, "Abs",     [ty, e])
DistApp(f, x)  = construct(DistExpr, "App",     [f, x])


function size_stlc(l::DistInductive{DistExpr})
    prob_match(l, [
        "Var"     => ()      -> DistUInt32(1),
        "Boolean" => () -> DistUInt32(1),
        "App"    => (e1, e2) -> size_stlc(e1) + size_stlc(e2),
        "Abs"    => (s, ty, e) -> DistUInt32(1) + depth(e),
    ])
end
