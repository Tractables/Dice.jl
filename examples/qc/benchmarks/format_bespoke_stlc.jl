gen_to_adnodes_of_interest = Dict(
  "W95_996_301_18_834_309_92Generator" => Dict{String, BigFloat}("tysz2_gen_type_tbool" => 0.9958860803834127581051798938551650402115284572008501804626740585442483264202683, "sz4_succ_var" => 0.5555135325826616876316829360539587311191383704357987682846567263119579498738498, "tysz1_gen_type_tbool" => 0.09521566167786227494703411688322314784521063687830728594787150178721132797032849, "sz0_zero_pr_var2" => 0.0687824377005745605607470735156207658872527409814467725025579728430270394444093, "sz2_succ_app" => 0.8278724576109117787246287871734912294251601472850537162286103361725250721408978, "sz4_succ_abs" => 0.3089005603911179785894971195614337115905026675150993991755571798932813518939221, "sz5_succ_var" => 0.5, "sz5_succ_abs" => 0.09240567375296773724251537845777818317289268263681539077022341985889458410328009, "sz2_succ_var" => 0.4629304115476302193408958980191130280350926767463319529650789792104391906327555, "sz1_succ_var" => 0.4189884820891497554413093111257656908271650448118762763984949205006515636272106, "sz1_succ_app" => 0.7028090439771752923143759607732418634618908287349296358317585240601663256212681, "sz1_succ_abs" => 0.300708665093580655296213140014473371494141827354513478876184406113679575172175, "sz3_succ_abs" => 0.8340466699407043515706136082425579210124096779460303058803963621511431869599463, "sz3_succ_app" => 0.06625733909610343061443835163605843772662998696847251842717139126879442614165382, "sz5_succ_app" => 0.7577063625047924641130832774155242967977919250538905987595813899869365994625273, "sz4_succ_app" => 0.6090613946482099584511599789979600158859488485459069513842262120756237096072077, "sz2_succ_abs" => 0.01846613009931596555302268641310159724057274188774880335653997283289146685775442, "sz3_succ_var" => 0.2301705815163302533709959537913487485267179537638742849599692474544065870654975),
)

OUT_DIR = "out"
mkpath(OUT_DIR)

function main()
    for (g, d) in gen_to_adnodes_of_interest
        path = joinpath(OUT_DIR, "$(g).v")
        if isfile(path)
            println("Error: file already exists at the following path:")
            println(path)
        else
            f = open(path, "w")
            println(f, format_bespoke_stlc(d))
            close(f)
        end
    end
end

thousandths(n) = Integer(round(n, digits=3) * 1000)

function format_bespoke_stlc(adnodes_of_interest)
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

(*
Derive (Arbitrary) for Typ.


(* Fixpoint genTyp (s: nat) : G Typ :=
  match s with
  | 0 => ret TBool
  | S s' => oneOf [
    t1 <- genTyp s' ;;
    t2 <- genTyp s' ;;
    ret (TFun t1 t2) ;
    ret TBool
    ]
  end.
   *)

(* #[export] Instance genArbitrary : GenSized Typ :=
{|
 arbitrarySized x := genTyp x
|}. *)

Definition genTyp (s: nat) : G Typ := arbitrary.

Fixpoint genOne (ctx: Ctx) (t: Typ) : G Expr :=
  match t with
  | TBool =>
    b <- arbitrary ;;
    ret (Bool b)
  | TFun t1 t2 =>
    t' <- genOne (t1 :: ctx) t2 ;;
    ret (Abs t1 t')
  end.


Fixpoint genVar' (ctx: Ctx) (t: Typ) (p: nat) (r: list nat) : list nat :=
  match ctx with
  | nil => r
  | t'::ctx' => if t == t' then genVar' ctx' t (p + 1) (p :: r)
                else genVar' ctx' t (p + 1) r
  end.


Definition genVar (ctx: Ctx) (t: Typ) : list (G Expr) :=
  let positions := genVar' ctx t 0 [] in
  let tf := (fun n => ret (Var n)) in
  map tf positions.


Fixpoint genExactExpr (f: nat) (ctx: Ctx) (t: Typ) : G Expr :=
  match f with
  | O => oneOf_ (genOne ctx t) (genOne ctx t :: genVar ctx t)
  | S f' =>
    let abs : list (G Expr) := match t with
              | TFun t1 t2 =>
                [bindGen (genExactExpr f' (t1 :: ctx) t2) (fun t' => 
                returnGen (Abs t1 t'))]
              | _ => nil
              end in
    let one := genOne ctx t in
    let app := 
      t' <- genTyp f' ;;
      e1 <- genExactExpr f' ctx (TFun t' t) ;;
      e2 <- genExactExpr f' ctx t' ;;
      ret (App e1 e2) in
    let var := genVar ctx t in
    
    oneOf_ one ([one] ++ abs ++ [app] ++ var)
  end.





Definition genExpr (s: nat) : G Expr :=
  t <- genTyp 3 ;;
  genExactExpr s [] t
.

#[export] Instance arbitrarySizedExpr : GenSized Expr :=
{|
  arbitrarySized s := genExpr s
|}.

Definition gTyped := genExpr 5.

Definition test_prop_SinglePreserve :=
  forAll gTyped (fun (e: Expr) =>
    prop_SinglePreserve e).

(* QuickChick test_prop_SinglePreserve. *)

Definition test_prop_MultiPreserve :=
  forAll gTyped (fun (e: Expr) =>
    prop_MultiPreserve e).

(* QuickChick test_prop_MultiPreserve. *)






*)
"""
end

main()