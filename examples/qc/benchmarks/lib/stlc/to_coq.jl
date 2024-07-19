function bespoke_stlc_to_coq(_p, adnodes_of_interest, _io)
    @assert issetequal(keys(adnodes_of_interest), ["sz1_succ_abs", "tysz2_gen_type_tbool", "sz3_succ_abs", "sz4_succ_var", "sz3_succ_app", "sz5_succ_app", "tysz1_gen_type_tbool", "sz0_zero_pr_var2", "sz2_succ_app", "sz4_succ_abs", "sz5_succ_var", "sz4_succ_app", "sz2_succ_abs", "sz5_succ_abs", "sz3_succ_var", "sz2_succ_var", "sz1_succ_var", "sz1_succ_app"])
    w(s) = thousandths(adnodes_of_interest[s])
    """
From QuickChick Require Import QuickChick. Import QcNotation.
From Coq Require Import Bool ZArith List. Import ListNotations.
From ExtLib Require Import Monad.
From ExtLib.Data.Monads Require Import OptionMonad.
Import MonadNotation.

From STLC Require Import Impl Spec.

Derive (Arbitrary) for Typ.
Derive (Arbitrary) for Expr.

Inductive bind : Ctx -> nat -> Typ -> Prop :=
| BindNow   : forall tau env, bind (tau :: env) 0 tau
| BindLater : forall tau tau' x env,
    bind env x tau -> bind (tau' :: env) (S x) tau.

Inductive typing (G : Ctx) : Expr -> Typ -> Prop :=
| TyVar :
    forall x T,
      bind G x T ->
      typing G (Var x) T
| TyBool :
    forall b,
      typing G (Bool b) TBool
| TyAbs :
    forall e T1 T2,
      typing (T1 :: G) e T2 ->
      typing G (Abs T1 e) (TFun T1 T2)
| TyApp :
    forall e1 e2 T1 T2,
      typing G e1 (TFun T1 T2) ->
      typing G e2 T1 ->
      typing G (App e1 e2) T2.


(* Look up in list of backtrack weights *)
Fixpoint get {a: Type} (l : list (nat * a)) (target_key : nat) (default : a): a :=
  match l with
  | [] =>
    (* This branch should never return *)
    default
  | (key, value) :: l' =>
    if Nat.eqb key target_key then
       value
    else get l' target_key default
  end.


#[export] Instance dec_type (t1 t2 : Typ) : Dec (t1 = t2).
Proof. dec_eq. Defined.
Derive Arbitrary for Typ.

Fixpoint genVar' (ctx: Ctx) (t: Typ) (p: nat) (r: list nat) : list nat :=
  match ctx with
  | nil => r
  | t'::ctx' =>
      if t = t'? then genVar' ctx' t (p + 1) (p :: r)
      else genVar' ctx' t (p + 1) r
  end.

Fixpoint genZero env tau : G (option Expr) :=
  match tau with
  | TBool =>
      bindGen arbitrary
              (fun b : bool =>
                 returnGen (Some (Bool b)))
  | TFun T1 T2 => 
      bindOpt
        (genZero (T1 :: env) T2)
        (fun e : Expr =>
           returnGen (Some (Abs T1 e)))
  end.

Fixpoint genTyp (s: nat) : G Typ :=
  match s with
  | 0 => ret TBool
  | S s' =>
    let '(boolWeight, funWeight) :=
      get
      [
        (1, ($(w("tysz1_gen_type_tbool")), 1000-$(w("tysz1_gen_type_tbool"))));
        (2, ($(w("tysz2_gen_type_tbool")), 1000-$(w("tysz2_gen_type_tbool"))))
      ]
      s
      (0, 0) in
    freq [
      (boolWeight, ret (TBool))
      ;
      (funWeight,
          t1 <- genTyp s';;
          t2 <- genTyp s';;
          ret (TFun t1 t2))
    ]
  end.

Fixpoint genExpr env tau (sz: nat) : G (option Expr) :=
  match sz with
  | 0 =>
    let '(var_weight, zero_weight) := ($(w("sz0_zero_pr_var2")), 1000-$(w("sz0_zero_pr_var2"))) in
      backtrack
        [(var_weight, oneOf_ (ret None) (map (fun x => returnGen (Some (Var x))) (genVar' env tau 0 [])))
        ;(zero_weight, genZero env tau)] 
  | S sz' =>
      let '(val_weight, app_weight, var_weight) :=
        get
          [
            (1, ($(w("sz1_succ_abs")), $(w("sz1_succ_app")), $(w("sz1_succ_var"))));
            (2, ($(w("sz2_succ_abs")), $(w("sz2_succ_app")), $(w("sz2_succ_var"))));
            (3, ($(w("sz3_succ_abs")), $(w("sz3_succ_app")), $(w("sz3_succ_var"))));
            (4, ($(w("sz4_succ_abs")), $(w("sz4_succ_app")), $(w("sz4_succ_var"))));
            (5, ($(w("sz5_succ_abs")), $(w("sz5_succ_app")), $(w("sz5_succ_var"))))
          ]
          sz
          (0, 0 ,0) in
      backtrack
        [(var_weight, oneOf_ (ret None) (map (fun x => returnGen (Some (Var x))) (genVar' env tau 0 [])))
         ;
        (app_weight,
          bindGen (genTyp 2)
                  (fun T1 : Typ =>
          bindOpt
            (genExpr env (TFun T1 tau) sz')
            (fun e1 : Expr =>
          bindOpt
            (genExpr env T1 sz')
            (fun e2 : Expr =>
               returnGen (Some (App e1 e2))))))
         ; 
         (val_weight,
           match tau with
           | TBool =>
               bindGen arbitrary
                       (fun b : bool =>
                          returnGen (Some (Bool b)))
           | TFun T1 T2 =>
               bindOpt
                 (genExpr (T1 :: env) T2 sz')
                    (fun e : Expr =>
                     returnGen (Some (Abs T1 e)))
              end)]
  end.

Definition gSized := 
    typ <- arbitrary ;;
    genExpr [] typ 5.


Definition test_prop_SinglePreserve :=
  forAllMaybe gSized (fun (e: Expr) =>
    prop_SinglePreserve e).

(*! QuickChick test_prop_SinglePreserve. *)
  
Definition test_prop_MultiPreserve :=
  forAllMaybe gSized (fun (e: Expr) =>
    prop_MultiPreserve e).
  
(*! QuickChick test_prop_MultiPreserve. *)

"""
end
