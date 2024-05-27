function gen_expr_lang(expr_size, typ_size)
  v = L.Var
  p = L.Param

  nil_typ() = L.Construct(ListTyp.T, :nil, [])
  cons_typ(hd, tl) = L.Construct(ListTyp.T, :cons, [hd, tl])

  nil_nat() = L.Construct(ListNat.T, :nil, [])
  cons_nat(hd, tl) = L.Construct(ListNat.T, :cons, [hd, tl])

  none_expr() = L.Construct(OptExpr.T, :None, [])
  some_expr(x) = L.Construct(OptExpr.T, :Some, [x])

  app(x, y) = L.Construct(Expr.T, :App, [x, y])
  var(n) = L.Construct(Expr.T, :Var, [n])
  abs(x, y) = L.Construct(Expr.T, :Abs, [x, y])
  bool(b) = L.Construct(Expr.T, :Bool, [b])

  tfun(x, y) = L.Construct(Typ.T, :TFun, [x, y])
  tbool() = L.Construct(Typ.T, :TBool, [])

  bind_opt_expr(x, sym, body) = L.BindGen(x, :_x,
    L.Match(v(:_x), [
      (:None, []) => L.ReturnGen(L.Construct(OptExpr.T, :None, [])),
      (:Some, [sym]) => body
    ])
  )

  genVar = L.Function("genVar'",
    [p(:ctx, Ctx.T), p(:t, Typ.T), p(:p, Nat.T), p(:r, ListNat.T)], ListNat.T,
    L.Match(v(:ctx), [
      (:nil, []) => v(:r),
      (:cons, [:t1, :ctx1]) => L.If(
        L.Eq(v(:t), v(:t1)),
        L.Call("genVar'", [v(:ctx1), v(:t), L.NatAdd([v(:p), L.Nat(1)]), cons_nat(v(:p), v(:r))]),
        L.Call("genVar'", [v(:ctx1), v(:t), L.NatAdd([v(:p), L.Nat(1)]), v(:r)]),
        )
    ])
  )

  
  genZero = L.Function("genZero", [p(:env, Ctx.T), p(:tau, Typ.T)], L.G{OptExpr.T},
    L.Match(v(:tau), [
      (:TBool, []) => L.BindGen(
        L.GenBool([]),
        :b,
        L.ReturnGen(some_expr(bool(v(:b))))
      ),
      (:TFun, [:T1, :T2]) => bind_opt_expr(
        L.Call("genZero", [cons_typ(v(:T1), v(:env)), v(:T2)]),
        :e, L.ReturnGen(some_expr(abs(v(:T1), v(:e))))
      )
    ])
  )

  genTyp = L.Function("genTyp", [p(:size, Nat.T)], L.G{Typ.T},
    L.Match(L.Var(:size), [
      (:O, []) => L.ReturnGen(tbool()),
      (:S, [:size1]) => L.Frequency([v(:size)], [
        "tbool" => L.ReturnGen(tbool()),
        "tfun" => L.BindGen(
          L.Call("genTyp", [v(:size1)]),
          :T1,
          L.BindGen(
            L.Call("genTyp", [v(:size1)]),
            :T2,
            L.ReturnGen(tfun(v(:T1), v(:T2)))
          )
        ),
      ])
    ])
  )

  genExpr = L.Function("genExpr",
    [p(:env, ListTyp.T), p(:tau, Typ.T), p(:size, Nat.T)], L.G{OptExpr.T},
    L.Match(L.Var(:size), [
      (:O, []) =>
        L.BindGen(
          L.Backtrack([v(:size)], [
            "var" => L.OneOf(
              L.ReturnGen(none_expr()),
              L.Map(
                L.Lambda([:x], L.ReturnGen(some_expr(var(v(:x))))),
                L.Call("genVar'", [v(:env), v(:tau), L.Nat(0), nil_nat()])
              )
            ),
            "zero" => L.Call("genZero", [v(:env), v(:tau)])
          ]),
        :res, L.ReturnGen(v(:res))),
      (:S, [:size1]) =>
        L.BindGen(
          L.Backtrack([v(:size)], [
            "var" => L.OneOf(
              L.ReturnGen(none_expr()),
              L.Map(
                L.Lambda([:x], L.ReturnGen(some_expr(var(v(:x))))),
                L.Call("genVar'", [v(:env), v(:tau), L.Nat(0), nil_nat()])
              )
            ),
            "app" => L.BindGen(
              L.Call("genTyp", [L.Nat(typ_size)]), :T1, 
              bind_opt_expr(
                L.Call("genExpr", [v(:env), tfun(v(:T1), v(:tau)), v(:size1)]),
                :e1,
                bind_opt_expr(
                  L.Call("genExpr", [v(:env), v(:T1), v(:size1)]),
                  :e2,
                  L.ReturnGen(some_expr(app(v(:e1), v(:e2))))
                )
              )
            ),
            "abs" => L.Match(v(:tau), [
              (:TBool, []) =>
                L.BindGen(L.GenBool([]), :b, L.ReturnGen(some_expr(bool(v(:b))))),
              (:TFun, [:T1, :T2]) =>
                bind_opt_expr(
                  L.Call("genExpr", [cons_typ(v(:T1), v(:env)), v(:T2), v(:size1)]),
                  :e, L.ReturnGen(some_expr(abs(v(:T1), v(:e))))
                )
            ])
          ]),
        :res, L.ReturnGen(v(:res)))
    ])
  )

  e = L.BindGen(
    L.Call("genTyp", [L.Nat(typ_size)]),
    :typ,
    L.Call("genExpr", [nil_typ(), v(:typ), L.Nat(expr_size)])
  )
  L.Program([genVar, genZero, genTyp, genExpr], e)
end
