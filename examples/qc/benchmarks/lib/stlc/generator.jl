# Based on
# https://github.com/jwshi21/etna/blob/main/bench-suite/Coq/STLC/Methods/BespokeGenerator.v



function gen_var(ctx::Ctx.t, t::Typ.t, p::DistNat, r::List{DistNat})::List{DistNat}
    match(ctx, [
        :nil => () -> r,
        :cons => (t′, ctx′) -> @dice_ite if prob_equals(t, t′)
            gen_var(ctx′, t, p + DistNat(1), DistCons(p, r))
        else
            gen_var(ctx′, t, p + DistNat(1), r)
        end
    ])
end

function bind_opt(f, ma::Opt.T{T})::Opt.T{<:Any} where T
    match(ma, [
        :None => () -> DistNone(T) # TODO: should be DistNone(return type of f)
        :Some => f
    ])
end

# TODO: try returning expr instead of opt extr? what does env do?
function gen_zero(env::Ctx.t, tau::Typ.t)
    match(tau, [
        :TBool => ()       -> DistSome(DistBoolean(flip(0.5))), # TODO: should this be constant for just learning structure?
        :TFun  => (T1, T2) -> bind_opt(gen_zero(DistCons(T1, env), T2)) do e
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

function gen_expr(rs::RunState, env::Ctx.t, tau::Typ.t, sz::Integer, gen_typ_sz::Integer, by_sz, track_return)::OptExpr.t
    track_return(
        begin
            for_prefix = if by_sz "sz$(sz)_" else "" end
            if sz == 0
                backtrack_for(rs, for_prefix * "zero", [
                    one_of(
                        map(Expr.t)(
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
                        map(Expr)(
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
                        :TBool => () -> DistSome(gen_bool()),
                        :TFun => (T1, T2) ->
                            bind_opt(gen_expr(rs, DistCons(T1, env), T2, sz′, gen_typ_sz, by_sz, track_return)) do e
                                DistSome(DistAbs(T1, e))
                            end
                    ]),
                ])
            end
        end
    )
end

function tb_gen_expr(rs::RunState, p, size::Integer, stack_tail, track_return)
    function get_dependent_dist(dependent)
        if     dependent == :size          size
        elseif dependent == :stack_tail    stack_tail
        else   error() end
    end
    dependent_dists = [get_dependent_dist(d) for d in p.dependents]
    track_return(
        if size == 0
            @dice_ite if flip_for(rs, "pvar", dependent_dists)
                Expr.Var(DistNat(0)) # really, this is arbitrary
            else
                Expr.Bool(true) # really, this is arbitrary
            end
        else
            sz′ = size - 1
            frequency_for(rs, "freq", dependent_dists, [
                "var" => begin
                    n = sum(
                        @dice_ite if flip_for(rs, "num$(n)", dependent_dists)
                            DistUInt32(n)
                        else
                            DistUInt32(0)
                        end
                        for n in twopowers(p.intwidth)
                    )
                    Expr.Var(n)
                end,
                "bool" => Expr.Bool(flip_for(rs, "ptrue", dependent_dists)),
                "abs" => begin
                    typ = tb_gen_type(rs, p, p.ty_size, update_stack_tail(p, stack_tail, 10))
                    e = tb_gen_expr(rs, p, sz′, update_stack_tail(p, stack_tail, 11), track_return)
                    Expr.Abs(typ, e)
                end,
                "app" => begin
                    e1 = tb_gen_expr(rs, p, sz′, update_stack_tail(p, stack_tail, 12), track_return)
                    e2 = tb_gen_expr(rs, p, sz′, update_stack_tail(p, stack_tail, 13), track_return)
                    Expr.App(e1, e2)
                end,
            ])
        end
    )
end

function tb_gen_type(rs::RunState, p, size::Integer, stack_tail)
    function get_dependent_dist(dependent)
        if     dependent == :size          size
        elseif dependent == :stack_tail    stack_tail
        else   error() end
    end
    dependent_dists = [get_dependent_dist(d) for d in p.ty_dependents]
    if size == 0
        Typ.TBool()
    else
        sz′ = size - 1
        @dice_ite if flip_for(rs, "ptbool", dependent_dists)
            Typ.TBool()
        else
            ty1 = tb_gen_type(rs, p, sz′, update_stack_tail(p, stack_tail, 14))
            ty2 = tb_gen_type(rs, p, sz′, update_stack_tail(p, stack_tail, 15))
            Typ.TFun(ty1, ty2)
        end
    end
end