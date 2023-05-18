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
        "Var"     => [DistNat],
        "Boolean" => [AnyBool],
        "Abs"     => [DistI{Typ}, DistI{Expr}],
        "App"     => [DistI{Expr}, DistI{Expr}],
    ]
end
DistVar(i)     = construct(Expr, "Var",     [i])
DistBoolean(b) = construct(Expr, "Boolean", [b])
DistAbs(ty, e) = construct(Expr, "Abs",     [ty, e])
DistApp(f, x)  = construct(Expr, "App",     [f, x])

function term_size(e::DistI{Expr})
    match(e, [
        "Var"     => (i)        -> DistUInt32(1),
        "Boolean" => (b)        -> DistUInt32(1),
        "App"     => (f, x)     -> DistUInt32(1) + term_size(f) + term_size(x),
        "Abs"     => (ty, e′)   -> DistUInt32(1) + term_size(e′),
    ])
end

function term_size(e::DistI{Opt{DistI{Expr}}})
    match(e, [
        "Some" => e -> term_size(e),
        "None" => () -> DistUInt32(1024),
    ])
end

function num_apps(e::DistI{Opt{DistI{Expr}}})
    match(e, [
        "Some" => x -> num_apps(x),
        "None" => () -> DistUInt32(1024),
    ])
end

function num_apps(e::DistI{Expr})
    match(e, [
        "Var"     => (i)        -> DistUInt32(0),
        "Boolean" => (b)        -> DistUInt32(0),
        "App"     => (f, x)    -> DistUInt32(1) + num_apps(f) + num_apps(x),
        "Abs"     => (ty, e′)  -> num_apps(e′),
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

function var_to_str(i)
    i += 1  # 1-idx
    vars = ["x", "y", "z"]
    if i <= length(vars)
        vars[i]
    else
        string('a' + i - length(vars))
    end
end

function stlc_str(ast, p=free, depth=0)
    name, children = ast
    if name == "Var"
        i, = children
        i isa Integer || (i = nat_ast_to_int(i))
        var_to_str(i)
    elseif name == "Boolean"
        v, = children
        string(v)
    elseif name == "Abs"
        ty, e = children
        parens(p > free, "λ$(var_to_str(depth + 1)):$(ty_str(ty)). $(stlc_str(e, free, depth + 1))")
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

