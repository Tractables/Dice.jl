# Define DistSTLC

module Typ
    using Dice
    @inductive t TBool() TFun(t, t)
end
type_to_coq(::Type{Typ.t}) = "Typ"

module Expr
    using Dice
    using Main: Nat, Typ
    @inductive t Var(Nat.t) Bool(AnyBool) Abs(Typ.t, t) App(t, t)
end
type_to_coq(::Type{Expr.t}) = "Expr"

module OptExpr
    using Dice
    using Main: Expr
    @inductive t None() Some(Expr.t)
end
type_to_coq(::Type{OptExpr.t}) = "option Expr"

module ListTyp
    using Dice
    using Main: Typ
    @inductive t nil() cons(Typ.t, t)
end
type_to_coq(::Type{ListTyp.t}) = "list Typ"

module ListNat
    using Dice
    @inductive t nil() cons(DistUInt32, t)
end
type_to_coq(::Type{ListNat.t}) = "list nat"

function prob_map(dest_module, f, l::ListNat.t)
    @match l [
        nil() -> dest_module.nil(),
        cons(hd, tl) -> dest_module.cons(f(hd), prob_map(dest_module, f, tl))
    ]
end

module ListOptExpr
    using Dice
    using Main: OptExpr
    @inductive t nil() cons(OptExpr.t, t)
end
type_to_coq(::Type{ListOptExpr.t}) = "list option Expr"

module Ctx
    using Dice
    using Main: Typ
    @inductive t nil() cons(Typ.t, t)
end
type_to_coq(::Type{Ctx.t}) = "Ctx"

function Base.length(l::ListOptExpr.t)
    @match l [
        nil() -> DistUInt32(0),
        cons(x, xs) -> DistUInt32(1) + length(xs),
    ]
end

function one_of(default::OptExpr.t, l::ListOptExpr.t)::OptExpr.t
    @match l [
        nil() -> default,
        cons(x, xs) -> @alea_ite if flip_reciprocal(length(l))
            x
        else
            one_of(default, xs)
        end
    ]
end

function one_of_sample(default::OptExpr.t, l::ListOptExpr.t)::OptExpr.t
    l::Dist = length(l)
    l = Dice.frombits(l, Dict())
    
    res = @match l [
        nil() -> default,
        cons(x, xs) -> if rand() < (1/length(l))
            x
        else
            one_of_sample(default, xs)
        end
    ]
    @assert isdeterministic(res)
    res
end


function size(e::Expr.t)
    match(e, [
        :Var     => (i)        -> DistUInt32(1),
        :Bool => (b)        -> DistUInt32(1),
        :App     => (f, x)     -> DistUInt32(1) + size(f) + size(x),
        :Abs     => (ty, e′)   -> DistUInt32(1) + size(e′),
    ])
end

function size(e::OptExpr.t)
    match(e, [
        :Some => e -> size(e),
        :None => () -> DistUInt32(1024),
    ])
end

function inv_size(e::OptExpr.t)
    match(e, [
        :Some => e -> inv_size(e),
        :None => () -> 1024
    ])
end

function inv_size(e::Expr.t)
    x::Number = Dice.frombits(size(e), Dict())
    1/x
end


function num_apps(e::OptExpr.t)
    match(e, [
        :Some => x -> num_apps(x),
        :None => () -> DistUInt32(1024),
    ])
end

function depth(e::OptExpr.t)
    @match e [
        Some(x) -> depth(x),
        None() -> DistUInt32(1024),
    ]
end

function depth(e::Expr.t)
    @match e [
        Var(i) -> DistUInt32(0),
        Bool(b) -> DistUInt32(0),
        App(f, x) -> DistUInt32(1) + max(depth(f), depth(x)),
        Abs(ty, e′) -> DistUInt32(1) + depth(e′)
    ]
end

function num_apps(e::Expr.t)
    match(e, [
        :Var     => (i)        -> DistUInt32(0),
        :Bool => (b)        -> DistUInt32(0),
        :App     => (f, x)    -> DistUInt32(1) + num_apps(f) + num_apps(x),
        :Abs     => (ty, e′)  -> num_apps(e′),
    ])
end

stlc_ctor_to_id = Dict(
    :Var => DistInt32(0),
    :Bool => DistInt32(1),
    :App => DistInt32(2),
    :Abs => DistInt32(3),
)

function ctor_to_id(ctor::Expr.t)
    match(ctor, [
        :Var => _ -> stlc_ctor_to_id[:Var]
        :Bool => _ -> stlc_ctor_to_id[:Bool]
        :App => (_, _) -> stlc_ctor_to_id[:App]
        :Abs => (_, _) -> stlc_ctor_to_id[:Abs]
    ])
end

function opt_ctor_to_id(opt_ctor::OptExpr.t)
    match(opt_ctor, [
        :Some => ctor_to_id,
        :None => () -> DistInt32(-1),
    ])
end

function collect_constructors(e)
    match(e, [
        :Var     => (i)        -> DistVector([stlc_ctor_to_id[:Var]]),
        :Bool => (b)        -> DistVector([stlc_ctor_to_id[:Bool]]),
        :App     => (f, x)    -> prob_append(prob_extend(collect_constructors(f), collect_constructors(x)), stlc_ctor_to_id[:App]),
        :Abs     => (ty, e′)  -> prob_append(collect_constructors(e′), stlc_ctor_to_id[:Abs]),
    ])
end

# https://stackoverflow.com/questions/59338968/printing-lambda-expressions-in-haskell

parens(b, s) = if b "($(s))" else s end

@enum StrfyCtx free=0 fun=1 arg=2

function ty_str(ty, free=true)
    name, children = ty
    name = Symbol(name)
    if name == :TBool
        # "Bool"
        "B"
    else
        t1, t2 = children
        parens(
            !free,
            # "$(ty_str(t1, false)) -> $(ty_str(t2, true))"
            "$(ty_str(t1, false))→$(ty_str(t2, true))"
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
    name = Symbol(name)
    if name == :Var
        i, = children
        i isa Integer || (i = nat_ast_to_int(i))
        # i is the number of steps from the *top* of the env, see gen_var
        var_depth = depth - i - 1
        var_str(var_depth)
    elseif name == :Bool
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
    Dice.frombits(x, Dict())
end

function typecheck(ast::Expr.t, gamma, depth=0)::Opt.T{Typ.t}
    @match ast [
        Var(i) -> begin
            var_depth = depth - to_int(i) - 1
            haskey(gamma, var_depth) || return Opt.None(Typ.t)
            Opt.Some(gamma[var_depth])
        end,
        Bool(_) -> Opt.Some(Typ.TBool()),
        Abs(t_in, e) -> begin
            gamma′ = copy(gamma)
            gamma′[depth] = t_in
            Opt.map(Typ.t, typecheck(e, gamma′, depth + 1)) do t_out
                Typ.TFun(t_in, t_out)
            end
        end,
        App(e1, e2) -> begin
            Opt.bind(Typ.t, typecheck(e1, gamma, depth)) do t1
                @match t1 [
                    TBool() -> Opt.None(Typ.t),
                    TFun(t1_in, t1_out) -> Opt.bind(Typ.t, typecheck(e2, gamma, depth)) do t2
                        if prob_equals(t1_in, t2)
                            Opt.Some(t1_out)
                        else
                            Opt.None(Typ.t)
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
    name = Symbol(name)
    if name == :Var
        i, = children
        i isa Integer || (i = nat_ast_to_int(i))
        var_depth = depth - i - 1
        if !haskey(gamma, var_depth)
            return "Unknown var $(var_str(var_depth))"
        end
        gamma[var_depth]
    elseif name == :Bool
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
