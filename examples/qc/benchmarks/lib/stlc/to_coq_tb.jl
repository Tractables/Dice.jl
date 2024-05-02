function typebased_stlc_to_coq(p, adnodes_vals, io)
    expected_matchid(s) = s in ["pvar", "ptbool", "freq_var", "freq_boolean", "freq_abs", "freq_app"]

    matchid_to_cases = Dict()
    for (name, val) in adnodes_vals
        matchid, case = split(name, "%%")
        @assert expected_matchid(matchid)
        case = "(" * join([tocoq(eval(Meta.parse(x))) for x in split(case, "%")], ", ") * ")"
        val = thousandths(val)
        push!(get!(matchid_to_cases, matchid, []), (case, val))
    end

    function mk_match(dependents, matchid)
        cases = matchid_to_cases[matchid]
        cases = sort(cases)
        if isnothing(dependents)
            "500"
        else
            "match ($(join(map(string, dependents), ","))) with 
$(join([" " ^ 9 * "| $(name) => $(w)" for (name, w) in cases], "\n"))
         | _ => 500
         end"
        end
    end
    
    """
From QuickChick Require Import QuickChick. Import QcNotation.
From Coq Require Import Bool ZArith List. Import ListNotations.
From ExtLib Require Import Monad.
From ExtLib.Data.Monads Require Import OptionMonad.
Import MonadNotation.

From STLC Require Import Impl Spec.

Fixpoint manual_gen_typ (size : nat) (last_callsite : nat) : G Typ :=
  match size with
  | 0 => returnGen TBool
  | S size' =>
      let weight_tbool := $(mk_match(p.ty_dependents, "ptbool")) in
      freq [ (weight_tbool, returnGen TBool);
      (1000 - weight_tbool,
      bindGen (manual_gen_typ size' 14)
        (fun p0 : Typ =>
         bindGen (manual_gen_typ size' 15)
           (fun p1 : Typ => returnGen (TFun p0 p1))))]
  end.

Fixpoint manual_gen_expr (size : nat) (last_callsite : nat) : G Expr :=
  match size with
  | 0 =>
      let weight_var := $(mk_match(p.dependents, "pvar")) in
      freq [ (weight_var, bindGen arbitrary (fun p0 : nat => returnGen (Var p0)));
      (1000 - weight_var, bindGen arbitrary (fun p0 : bool => returnGen (Bool p0)))]
  | S size' =>
      let weight_var := $(mk_match(p.dependents, "freq_var")) in
      let weight_boolean := $(mk_match(p.dependents, "freq_boolean")) in
      let weight_abs := $(mk_match(p.dependents, "freq_abs")) in
      let weight_app := $(mk_match(p.dependents, "freq_app")) in
      freq [ (weight_var,
      bindGen arbitrary (fun p0 : nat => returnGen (Var p0)));
      (weight_boolean, bindGen arbitrary (fun p0 : bool => returnGen (Bool p0)));
      (weight_abs,
      bindGen (manual_gen_typ $(p.ty_size) 10)
        (fun p0 : Typ =>
         bindGen (manual_gen_expr size' 11)
           (fun p1 : Expr => returnGen (Abs p0 p1))));
      (weight_app,
      bindGen (manual_gen_expr size' 12)
        (fun p0 : Expr =>
         bindGen (manual_gen_expr size' 13)
           (fun p1 : Expr => returnGen (App p0 p1))))]
  end.

Definition gSized :=
  manual_gen_expr $(p.size) 20.
  
Definition test_prop_SinglePreserve :=
  forAll gSized (fun (e: Expr) =>
    prop_SinglePreserve e).

(*! QuickChick test_prop_SinglePreserve. *)
  
Definition test_prop_MultiPreserve :=
  forAll gSized (fun (e: Expr) =>
    prop_MultiPreserve e).
  
(*! QuickChick test_prop_MultiPreserve. *)

"""
end
