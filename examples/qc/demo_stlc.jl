using Revise
using Dice
include("lib/uint_match.jl")
include("lib/dist_stlc.jl")
include("lib/sample.jl")

DistNat = DistUInt32
Ctx = DistI{List{DistI{Typ}}}

function gen_var(ctx::Ctx, t::DistI{Typ}, p::DistNat, r::DistI{List{DistNat}})::DistI{List{DistNat}}
    match(ctx, [
        "Nil" => () -> r,
        "Cons" => (t′, ctx′) -> @dice_ite if prob_equals(t, t′)
            gen_var(ctx′, t, p + Nat(1), DistCons(p, r))
        else
            gen_var(ctx′, t, p + Nat(1), r)
        end
    ])
end

function bind_opt(f, ma::DistI{Opt{T}})::DistI{<:Opt{<:Any}} where T
    match(ma, [
        "None" => () -> DistNone(T)
        "Some" => f
    ])
end

function gen_zero(env::Ctx, tau::DistI{Typ})
    match(tau, [
        "TBool" => ()       -> DistSome(DistBoolean(flip(0.5))),
        "TFun"  => (T1, T2) -> bind_opt(gen_zero(DistCons(T1, env), T2)) do e
            DistSome(DistAbs(T1, e))
        end
    ])
end

flip_reciprocal(x) = prob_equals(DistUInt32(0), Dice.unif_half(x))

# TODO: test
function one_of(l::DistI{List{T}})::DistI{Opt{T}} where T <: Dist
    match(l, [
        "Nil" => () -> DistNone(T),
        "Cons" => (x, xs) -> @dice_ite if flip_reciprocal(length(l))
            DistSome(x)
        else
            one_of(xs)
        end
    ])
end

function backtrack(::Type{T}, thunks)::DistI{Opt{T}} where T
    _backtrack(T, Iterators.Stateful(thunks))
end

function _backtrack(::Type{T}, thunks)::DistI{Opt{T}} where T
    isempty(thunks) && return DistNone(T)
    match(popfirst!(thunks)(), [
        "Some" => x -> DistSome(x),
        "None" => () -> _backtrack(T, thunks)
    ])
end

function _backtrack(::Type{T}, thunks)::DistI{Opt{T}} where T
    res = DistNone(T)
    for thunk in thunks
        res = @dice_ite if matches(res, "Some")
            res
        else
            thunk()
        end
    end
    res
end

function map(::Type{RetT}) where RetT
    function inner(f, l::DistI{List{T}}) where T
        match(l, [
            "Nil" => () -> DistNil(RetT),
            "Cons" => (x, xs) -> DistCons(f(x), map(RetT)(f, xs))
        ])
    end
end

# TODO: how is Arbitrary derived for type in BespokeGenerator.v?
function gen_type(size)
    @dice_ite if size == 0 || flip_for("gen_type_tbool")
        DistTBool()
    else
        DistTFun(gen_type(size - 1), gen_type(size - 1))
    end
end

gen_type() = gen_type(1)

function gen_expr(env::Ctx, tau::DistI{Typ}, sz::DistNat)::DistI{Opt{DistI{Expr}}}
    match(sz, [
        "Zero" => () -> backtrack(DistI{Expr}, [
            () -> one_of(
                map(DistI{Expr})(
                    DistVar,
                    gen_var(env, tau, zero(DistNat), DistNil(DistNat))
                )
            ),
            () -> gen_zero(env, tau)
        ]),
        "Succ" => sz′ -> backtrack(DistI{Expr}, [
            # Var
            () -> one_of(
                map(DistI{Expr})(
                    DistVar,
                    gen_var(env, tau, zero(DistNat), DistNil(DistNat))
                )
            ),
            # App
            () -> begin
                T1 = gen_type()
                bind_opt(gen_expr(env, DistTFun(T1, tau), sz′)) do e1
                    bind_opt(gen_expr(env, T1, sz′)) do e2
                        DistSome(DistApp(e1, e2))
                    end
                end
            end,
            # Value
            () -> match(tau, [
                "TBool" => () -> DistSome(DistBoolean(flip(0.5))),
                "TFun" => (T1, T2) ->
                    bind_opt(gen_expr(DistCons(T1, env), T2, sz′)) do e
                        DistSome(DistAbs(T1, e))
                    end
            ])
        ]),
    ])
end

INIT_SIZE = 1

@show INIT_SIZE

e = gen_expr(DistNil(DistI{Typ}), gen_type(), DistUInt32(INIT_SIZE))
println("generated")
dist = pr(e)
display(dist)
println()

@show dist
println()

println("Top 10 in detail")
for (x, pr) in collect(dist)[1:10]
    println("pr: $(pr)")
    name, ast = x
    if name == "None"
        println(name)
    else
        println(stlc_str(ast[1]))
    end
    println()
end