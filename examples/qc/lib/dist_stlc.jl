# Define DistSTLC

struct Typ <: InductiveType end
function Dice.param_lists(::Type{Typ})
    [
        "TBool" => [],
        "TFun"  => [DistI{Typ}, DistI{Typ}],
    ]
end
DistTBool()          = construct(Typ, "TBool", [])
DistTFun(f_ty, x_ty) = construct(Typ, "TFun",  [f_ty, x_ty])

struct Expr <: InductiveType end
function Dice.param_lists(::Type{Expr})
    [
        "Var"     => [DistUInt32],
        "Boolean" => [AnyBool],
        "Abs"     => [DistI{Typ}, DistI{Expr}],
        "App"     => [DistI{Expr}, DistI{Expr}],
    ]
end
DistVar(i)     = construct(Expr, "Var",     [i])
DistBoolean(b) = construct(Expr, "Boolean", [b])
DistAbs(ty, e) = construct(Expr, "Abs",     [ty, e])
DistApp(f, x)  = construct(Expr, "App",     [f, x])

function size_stlc(l::DistI{Expr})
    match(l, [
        "Var"     => (i)      -> DistUInt32(1),
        "Boolean" => () -> DistUInt32(1),
        "App"    => (e1, e2) -> size_stlc(e1) + size_stlc(e2),
        "Abs"    => (s, ty, e) -> DistUInt32(1) + depth(e),
    ])
end

# https://stackoverflow.com/questions/59338968/printing-lambda-expressions-in-haskell

parens(b, s) = if b "($(s))" else s end

@enum StrfyCtx free=0 fun=1 arg=2

function ty_str(ty, free=true)
    name, children = ty
    if name == "TBool"
        "Bool"
    else
        t1, t2 = children
        parens(
            !free,
            "$(ty_str(t1, false)) -> $(ty_str(t2, true))"
        )
    end
end

function stlc_str(ast, p=free, depth=0)
    name, children = ast
    vars = ["x", "y", "z"]
    if name == "Var"
        i, = children
        if i <= length(vars)
            vars[i]
        else
            string('a' + i - length(vars))
        end
    elseif name == "Boolean"
        v, = children
        string(v)
    elseif name == "Abs"
        ty, e = children
        parens(p > free, "λ$(vars[depth + 1]):$(ty_str(ty)). $(stlc_str(e, free, depth + 1))")
    elseif name == "App"
        e1, e2 = children
        parens(
            p > fun,
            "$(stlc_str(e1, fun, depth)) $(stlc_str(e2, arg, depth))"
        )
    else
        error("Bad node $(name)")
    end
end

