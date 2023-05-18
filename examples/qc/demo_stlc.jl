using Dice
include("lib/dist_stlc.jl")
include("lib/stlc_util.jl")

############################
# Config
############################

INIT_SIZE = 1
# DistNat = DistUInt32  # Binary encoding
DistNat = DistI{Nat}  # Peano/inductive encoding
METRIC = num_apps

############################

Ctx = DistI{List{DistI{Typ}}}

function gen_var(ctx::Ctx, t::DistI{Typ}, p::DistNat, r::DistI{List{DistNat}})::DistI{List{DistNat}}
    match(ctx, [
        "Nil" => () -> r,
        "Cons" => (t′, ctx′) -> @dice_ite if prob_equals(t, t′)
            gen_var(ctx′, t, p + DistNat(1), DistCons(p, r))
        else
            gen_var(ctx′, t, p + DistNat(1), r)
        end
    ])
end

function bind_opt(f, ma::DistI{Opt{T}})::DistI{<:Opt{<:Any}} where T
    match(ma, [
        "None" => () -> DistNone(T)
        "Some" => f
    ])
end

# TODO: try returning expr instead of opt extr? what does env do?
function gen_zero(env::Ctx, tau::DistI{Typ})
    match(tau, [
        "TBool" => ()       -> DistSome(DistBoolean(flip(0.5))),
        "TFun"  => (T1, T2) -> bind_opt(gen_zero(DistCons(T1, env), T2)) do e
            DistSome(DistAbs(T1, e))
        end
    ])
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
        "Zero" => () -> backtrack_for("zero", [
            one_of(
                map(DistI{Expr})(
                    DistVar,
                    gen_var(env, tau, zero(DistNat), DistNil(DistNat))
                )
            ),
            gen_zero(env, tau)
        ]),
        "Succ" => sz′ -> backtrack_for("succ", [
            # Var
            one_of(
                map(DistI{Expr})(
                    DistVar,
                    gen_var(env, tau, zero(DistNat), DistNil(DistNat))
                )
            ),
            # App
            begin
                T1 = gen_type()
                bind_opt(gen_expr(env, DistTFun(T1, tau), sz′)) do e1
                    bind_opt(gen_expr(env, T1, sz′)) do e2
                        DistSome(DistApp(e1, e2))
                    end
                end
            end,
            # Value
            match(tau, [
                "TBool" => () -> DistSome(DistBoolean(flip(0.5))),
                "TFun" => (T1, T2) ->
                    bind_opt(gen_expr(DistCons(T1, env), T2, sz′)) do e
                        DistSome(DistAbs(T1, e))
                    end
            ]),
        ]),
    ])
end


println("== Config ==")
@show INIT_SIZE
@show DistNat
println()

println("gen_expr()")
@time e = gen_expr(DistNil(DistI{Typ}), gen_type(), DistNat(INIT_SIZE))
println()

println("pr($(METRIC)(e))")
@time metric_dist = pr(METRIC(e))
println(metric_dist)
println()

pr_none = pr(matches(e, "None"))[true]
println("Probability of none: $(pr_none)")
println()

if INIT_SIZE <= 2
    println("Getting distribution of all exprs")
    @time dist = pr(e)
    for (k, pr) in dist
        println("pr: $(pr)")
        println(opt_stlc_str(k))
        println()
    end
else
    println("A few sampled exprs:")
    for _ in 1:10
        expr = sample(e)
        println(opt_stlc_str(expr))
    end
end
