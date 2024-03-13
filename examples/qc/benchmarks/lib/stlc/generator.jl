# Based on
# https://github.com/jwshi21/etna/blob/main/bench-suite/Coq/STLC/Methods/BespokeGenerator.v


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
        "None" => () -> DistNone(T) # TODO: should be DistNone(return type of f)
        "Some" => f
    ])
end

# TODO: try returning expr instead of opt extr? what does env do?
function gen_zero(env::Ctx, tau::DistI{Typ})
    match(tau, [
        "TBool" => ()       -> DistSome(DistBoolean(flip(0.5))), # TODO: should this be constant for just learning structure?
        "TFun"  => (T1, T2) -> bind_opt(gen_zero(DistCons(T1, env), T2)) do e
            DistSome(DistAbs(T1, e))
        end
    ])
end

function gen_type(rs, sz, by_sz)
    group = if by_sz "tysz$(sz)_" else "" end * "gen_type_tbool"
    @dice_ite if sz == 0 || flip(register_weight!(rs, group))
        DistTBool()
    else
        DistTFun(gen_type(rs, sz - 1, by_sz), gen_type(rs, sz - 1, by_sz))
    end
end

function gen_bool()
    DistBoolean(flip(0.5))
end

function gen_expr(rs::RunState, env::Ctx, tau::DistI{Typ}, sz::Integer, gen_typ_sz::Integer, by_sz, track_return)::DistI{Opt{DistI{Expr}}}
    track_return(
        begin
            for_prefix = if by_sz "sz$(sz)_" else "" end
            if sz == 0
                backtrack_for(rs, for_prefix * "zero", [
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
                backtrack_for(rs, for_prefix * "succ", [
                    # Var
                    one_of(
                        map(DistI{Expr})(
                            DistVar,
                            gen_var(env, tau, zero(DistNat), DistNil(DistNat))
                        )
                    ),
                    # App
                    begin
                        T1 = gen_type(rs, gen_typ_sz, by_sz)
                        bind_opt(gen_expr(rs, env, DistTFun(T1, tau), sz′, gen_typ_sz, by_sz, track_return)) do e1
                            bind_opt(gen_expr(rs, env, T1, sz′, gen_typ_sz, by_sz, track_return)) do e2
                                DistSome(DistApp(e1, e2))
                            end
                        end
                    end,
                    # Value
                    match(tau, [
                        "TBool" => () -> DistSome(gen_bool()),
                        "TFun" => (T1, T2) ->
                            bind_opt(gen_expr(rs, DistCons(T1, env), T2, sz′, gen_typ_sz, by_sz, track_return)) do e
                                DistSome(DistAbs(T1, e))
                            end
                    ]),
                ])
            end
        end
    )
end

function tb_gen_expr(rs::RunState, sz::Integer, ty_sz, track_return)
    track_return(
        if sz == 0
            @dice_ite if flip(register_weight!(rs, "sz$(sz)_pvar"))
                DistVar(DistNat(0)) # really, this is arbitrary
            else
                DistBoolean(true) # really, this is arbitrary
            end
        else
            sz′ = sz - 1
            frequency_for(rs, "sz$(sz)_freq", [
                DistVar(DistNat(0)), # really, this is arbitrary
                DistBoolean(true), # really, this is arbitrary
                begin
                    typ = tb_gen_type(ty_sz) # TODO
                    e = tb_gen_expr(rs, sz′, ty_sz, track_return)
                    DistAbs(typ, e)
                end,
                begin
                    e1 = tb_gen_expr(rs, sz′, ty_sz, track_return)
                    e2 = tb_gen_expr(rs, sz′, ty_sz, track_return)
                    DistApp(e1, e2)
                end,
            ])
        end
    )
end

function tb_gen_type(rs::RunState, sz::Integer)
    if sz == 0
        DistTBool()
    else
        sz′ = sz - 1
        @dice_ite if flip(register_weight!(rs, "tysz$(sz)_ptbool"))
            DistTBool()
        else
            ty1 = tb_gen_type(rs, sz′)
            ty2 = tb_gen_type(rs, sz′)
            DistTFun(ty1, ty2)
        end
    end
end