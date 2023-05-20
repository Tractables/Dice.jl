# Based on
# https://github.com/jwshi21/etna/blob/main/bench-suite/Coq/STLC/Methods/BespokeGenerator.v

# Encoding: DistUInt32 for binary; DistI{Nat} for Peano
# Shouldn't affect results
DistNat = DistUInt32

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

function gen_type(sz, by_sz)
    for_prefix = if by_sz "$(sz)_" else "" end
    @dice_ite if sz == 0 || flip_for(for_prefix * "gen_type_tbool")
        DistTBool()
    else
        DistTFun(gen_type(sz - 1, by_sz), gen_type(sz - 1, by_sz))
    end
end

function gen_bool()
    DistBoolean(flip(0.5))
end

function gen_expr(env::Ctx, tau::DistI{Typ}, sz::Integer, gen_typ_sz::Integer, by_sz)::DistI{Opt{DistI{Expr}}}
    for_prefix = if by_sz "$(sz)_" else "" end
    if sz == 0
        backtrack_for(for_prefix * "zero", [
            one_of(
                map(DistI{Expr})(
                    DistVar,
                    gen_var(env, tau, zero(DistNat), DistNil(DistNat))
                )
            ),
            gen_zero(env, tau)
        ])
    else
        sz′ = sz - 1
        backtrack_for(for_prefix * "succ", [
            # Var
            one_of(
                map(DistI{Expr})(
                    DistVar,
                    gen_var(env, tau, zero(DistNat), DistNil(DistNat))
                )
            ),
            # App
            begin
                T1 = gen_type(gen_typ_sz, by_sz)
                bind_opt(gen_expr(env, DistTFun(T1, tau), sz′, gen_typ_sz, by_sz)) do e1
                    bind_opt(gen_expr(env, T1, sz′, gen_typ_sz, by_sz)) do e2
                        DistSome(DistApp(e1, e2))
                    end
                end
            end,
            # Value
            match(tau, [
                "TBool" => () -> DistSome(gen_bool()),
                "TFun" => (T1, T2) ->
                    bind_opt(gen_expr(DistCons(T1, env), T2, sz′, gen_typ_sz, by_sz)) do e
                        DistSome(DistAbs(T1, e))
                    end
            ]),
        ])
    end
end
