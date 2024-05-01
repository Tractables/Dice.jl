# Define DistSTLC

module Typ
    using Dice
    @inductive T TBool() TFun(T, T)
end

module Expr
    using Dice
    using Main: DistNat, Typ
    @inductive T Var(DistNat) Boolean(AnyBool) Abs(Typ.T, T) App(T, T)
end

function term_size(e::Expr.T)
    match(e, [
        :Var     => (i)        -> DistUInt32(1),
        :Boolean => (b)        -> DistUInt32(1),
        :App     => (f, x)     -> DistUInt32(1) + term_size(f) + term_size(x),
        :Abs     => (ty, e′)   -> DistUInt32(1) + term_size(e′),
    ])
end

function term_size(e::Opt.T{Expr.T})
    match(e, [
        :Some => e -> term_size(e),
        :None => () -> DistUInt32(1024),
    ])
end

function num_apps(e::Opt.T{Expr.T})
    match(e, [
        :Some => x -> num_apps(x),
        :None => () -> DistUInt32(1024),
    ])
end

function num_apps(e::Expr.T)
    match(e, [
        :Var     => (i)        -> DistUInt32(0),
        :Boolean => (b)        -> DistUInt32(0),
        :App     => (f, x)    -> DistUInt32(1) + num_apps(f) + num_apps(x),
        :Abs     => (ty, e′)  -> num_apps(e′),
    ])
end

stlc_ctor_to_id = Dict(
    :Var => DistInt32(0),
    :Boolean => DistInt32(1),
    :App => DistInt32(2),
    :Abs => DistInt32(3),
)

function ctor_to_id(ctor::Expr.T)
    match(ctor, [
        :Var => _ -> stlc_ctor_to_id[:Var]
        :Boolean => _ -> stlc_ctor_to_id[:Boolean]
        :App => (_, _) -> stlc_ctor_to_id[:App]
        :Abs => (_, _) -> stlc_ctor_to_id[:Abs]
    ])
end

function opt_ctor_to_id(opt_ctor::Opt.T{Expr.T})
    match(opt_ctor, [
        :Some => ctor_to_id,
        :None => () -> DistInt32(-1),
    ])
end

function collect_constructors(e)
    match(e, [
        :Var     => (i)        -> DistVector([stlc_ctor_to_id[:Var]]),
        :Boolean => (b)        -> DistVector([stlc_ctor_to_id[:Boolean]]),
        :App     => (f, x)    -> prob_append(prob_extend(collect_constructors(f), collect_constructors(x)), stlc_ctor_to_id[:App]),
        :Abs     => (ty, e′)  -> prob_append(collect_constructors(e′), stlc_ctor_to_id[:Abs]),
    ])
end

# https://stackoverflow.com/questions/59338968/printing-lambda-expressions-in-haskell

parens(b, s) = if b "($(s))" else s end

@enum StrfyCtx free=0 fun=1 arg=2

function ty_str(ty, free=true)
    name, children = ty
    if name == :TBool
        "Bool"
    else
        t1, t2 = children
        parens(
            !free,
            "$(ty_str(t1, false)) -> $(ty_str(t2, true))"
        )
    end
end

function var_str(i)
    i += 1  # 1-idx
    vars = ["x", "y", "z", "w"]
    if i <= 0
        "badvar_$(i)"
    elseif i <= length(vars)
        vars[i]
    else
        string('a' + i - length(vars) - 1)
    end
end

function stlc_str(ast, depth=0, p=free)
    name, children = ast
    if name == :Var
        i, = children
        i isa Integer || (i = nat_ast_to_int(i))
        # i is the number of steps from the *top* of the env, see gen_var
        var_depth = depth - i - 1
        var_str(var_depth)
    elseif name == :Boolean
        v, = children
        string(v)
    elseif name == :Abs
        ty, e = children
        parens(p > free, "λ$(var_str(depth)):$(ty_str(ty)). $(stlc_str(e, depth + 1, free))")
    elseif name == :App
        e1, e2 = children
        parens(
            p > fun,
            "$(stlc_str(e1, depth, fun)) $(stlc_str(e2, depth, arg))"
        )
    else
        error("Bad node $(name)")
    end
end

# ironic abuse of types
function error_ty(ty)
    ty isa AbstractString
end

function get_error(ty)
    ty
end

function opt_map(f, x::Tuple)
    name, children = x
    if name == :Some
        e, = children
        f(e)
    elseif name == :None
        nothing
    else
        error()
    end
end

function opt_map(f, x::Opt.T)
    @match x [
        None() -> nothing,
        Some(x) -> f(x),
    ]
end

function diff_test_typecheck(expr_dist, expr)
    @assert isdeterministic(expr_dist)
    opt_map(expr_dist) do expr_dist
        opt_map(expr) do expr
            ty1 = typecheck(expr)
            ty2_dist = pr(typecheck(expr_dist))
            @assert length(ty2_dist) == 1
            ty2 = first(keys(ty2_dist))
            if error_ty(ty1)
                @assert ty2 == (:None, [])
            else
                @assert ty2 == (:Some, [ty1]) "$ty1 $ty2"
            end
        end
    end
end

function to_int(x::DistUInt32)
    dist = pr(x)
    @assert length(dist) == 1
    first(keys(dist))
end

function typecheck(ast::Expr.T, gamma, depth=0)::Opt.T{Typ.T}
    @match ast [
        Var(i) -> begin
            var_depth = depth - to_int(i) - 1
            haskey(gamma, var_depth) || return Opt.None(Typ.T)
            Opt.Some(gamma[var_depth])
        end,
        Boolean(_) -> Opt.Some(Typ.TBool()),
        Abs(t_in, e) -> begin
            gamma′ = copy(gamma)
            gamma′[depth] = t_in
            Opt.map(Typ.T, typecheck(e, gamma′, depth + 1)) do t_out
                Typ.TFun(t_in, t_out)
            end
        end,
        App(e1, e2) -> begin
            Opt.bind(Typ.T, typecheck(e1, gamma, depth)) do t1
                @match t1 [
                    TBool() -> Opt.None(Typ.T),
                    TFun(t1_in, t1_out) -> Opt.bind(Typ.T, typecheck(e2, gamma, depth)) do t2
                        if prob_equals(t1_in, t2)
                            Opt.Some(t1_out)
                        else
                            Opt.None(Typ.T)
                        end
                    end,
                ]
            end
        end,
    ]
end

function typecheck_opt(ast)
    name, children = ast
    if name == :Some
        e, = children
        ty = typecheck(e)
        if error_ty(ty)
            println("Failed to typecheck $(stlc_str(e))")
            println(get_error(ty))
            println()
        end
    elseif name == :None
        # do nothing
    else
        error("Bad node $(name)")
    end
end

typecheck(ast) = typecheck(ast, Dict())

function typecheck(ast::Tuple, gamma, depth=0)
    name, children = ast
    if name == :Var
        i, = children
        i isa Integer || (i = nat_ast_to_int(i))
        var_depth = depth - i - 1
        if !haskey(gamma, var_depth)
            return "Unknown var $(var_str(var_depth))"
        end
        gamma[var_depth]
    elseif name == :Boolean
        (:TBool, [])
    elseif name == :Abs
        t_in, e = children
        gamma′ = copy(gamma)
        gamma′[depth] = t_in
        t_out = typecheck(e, gamma′, depth + 1)
        error_ty(t_out) && return t_out
        (:TFun, [t_in, t_out])
    elseif name == :App
        e1, e2 = children
        t1 = typecheck(e1, gamma, depth)
        error_ty(t1) && return t1
        if t1[1] != :TFun
            return "\"$(stlc_str(e1, depth))\" typechecked to $(ty_str(t1)), expected function"
        end
        t2 = typecheck(e2, gamma, depth)
        error_ty(t2) && return t2
        t1_in, t1_out = t1[2]
        if t1_in != t2
            return "Expected \"$(stlc_str(e2, depth))\" to be $(ty_str(t1_in)), got $(ty_str(t2))"
        end
        t1_out
    else
        error("Bad node $(name)")
    end
end

function eq_except_numbers(x::Typ.T, y::Typ.T)
    @match x [
        TBool() -> (@match y [
            TBool() -> true,
            TFun(_, _) -> false,
        ]),
        TFun(a1, b1) -> (@match y [
            TBool() -> false,
            TFun(a2, b2) -> eq_except_numbers(a1, a2) & eq_except_numbers(b1, b2),
        ]),
    ]
end

function eq_except_numbers(x::Expr.T, y::Expr.T)
    @match x [
        Var(_) -> (@match y [
            Var(_) -> true,
            Boolean(_) -> false,
            App(_, _) -> false,
            Abs(_, _) -> false,
        ]),
        Boolean(_) -> (@match y [
            Var(_) -> false,
            Boolean(_) -> true,
            App(_, _) -> false,
            Abs(_, _) -> false,
        ]),
        App(f1, x1) -> (@match y [
            Var(_) -> false,
            Boolean(_) -> false,
            App(f2, x2) -> eq_except_numbers(f1, f2) & eq_except_numbers(x1, x2),
            Abs(_, _) -> false,
        ]),
        Abs(ty1, e1) -> (@match y [
            Var(_) -> false,
            Boolean(_) -> false,
            App(_, _) -> false,
            Abs(ty2, e2) -> eq_except_numbers(ty1, ty2) & eq_except_numbers(e1, e2),
        ]),
    ]
end

function eq_except_numbers(x::Opt.T{T}, y::Opt.T{T}) where T
    @match x [
        Some(xv) -> (@match y [
            Some(yv) -> eq_except_numbers(xv, yv),
            None() -> false,
        ]),
        None() -> (@match y [
            Some(_) -> false,
            None() -> true,
        ])
    ]
end