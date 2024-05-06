function typebased_bst_to_coq(p, adnodes_vals, io)
    expected_matchid(s) = s in ["leaf", ["num$(n)" for n in twopowers(p.intwidth)]...]

    matchid_to_cases = Dict()
    for (name, val) in adnodes_vals
        matchid, case = split(name, "%%")
        @assert expected_matchid(matchid) matchid
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
From Coq Require Import List. Import ListNotations.
From Coq Require Import ZArith.
From ExtLib Require Import Monad.
Import MonadNotation.

From BST Require Import Impl.
From BST Require Import Spec.

Fixpoint manual_gen_tree (size : nat) (last_callsite : nat) : G Tree := 
  match size with
  | 0 => returnGen E
  | S size' =>
      let weight_leaf := $(mk_match(p.leaf_dependents, "leaf")) in
      freq [
      (weight_leaf,
      returnGen E);
      (1000-weight_leaf,
      bindGen (manual_gen_tree size' 10)
        (fun p0 : Tree =>
$(
    join(
        ["         let weight_$(n) := $(mk_match(p.num_dependents, "num$(n)")) in"
        for n in twopowers(p.intwidth)],
        "\n"
    )
)
$(
    join(
        [
"bindGen (freq [ (weight_$(n), returnGen $(n)); (1000-weight_$(n), returnGen 0)])
(fun n$(n) : nat => "
        for n in twopowers(p.intwidth)],
        "\n"
    )
)
let p1 := $(join(["n$(n)" for n in twopowers(p.intwidth)], "+")) in
            bindGen arbitrary
              (fun p2 : nat =>
               bindGen (manual_gen_tree size' 11)
                 (fun p3 : Tree => returnGen (T p0 p1 p2 p3)))
                 $(")" ^ p.intwidth) 
                 ))]
  end.

Definition gSized : G Tree :=
  manual_gen_tree $(p.size) 20.

Definition manual_shrink_tree := 
    fun x : Tree =>
    let
      fix aux_shrink (x' : Tree) : list Tree :=
        match x' with
        | E => []
        | T p0 p1 p2 p3 =>
            ([p0] ++
             map (fun shrunk : Tree => T shrunk p1 p2 p3) (aux_shrink p0) ++
             []) ++
            (map (fun shrunk : nat => T p0 shrunk p2 p3) (shrink p1) ++ []) ++
            (map (fun shrunk : nat => T p0 p1 shrunk p3) (shrink p2) ++ []) ++
            ([p3] ++
             map (fun shrunk : Tree => T p0 p1 p2 shrunk) (aux_shrink p3) ++
             []) ++ []
        end in
    aux_shrink x.


#[global]
Instance shrTree : Shrink (Tree) := 
  {| shrink x := manual_shrink_tree x |}.

Definition test_prop_InsertValid   :=
  forAll gSized (fun (t: Tree)  =>
  forAll arbitrary (fun (k: nat)  =>
  forAll arbitrary (fun (v: nat) =>
  prop_InsertValid t k v)))
.

(*! QuickChick test_prop_InsertValid. *)

Definition test_prop_DeleteValid   :=
  forAll gSized (fun (t: Tree)  =>
  forAll arbitrary (fun (k: nat) =>
  prop_DeleteValid t k))
.

(*! QuickChick test_prop_DeleteValid. *)


Definition test_prop_UnionValid    :=
  forAll gSized (fun (t1: Tree)  =>
  forAll gSized (fun (t2: Tree) =>
  prop_UnionValid t1 t2))
.

(*! QuickChick test_prop_UnionValid. *)

Definition test_prop_InsertPost    :=
  forAll gSized (fun (t: Tree)  =>
  forAll arbitrary (fun (k: nat)  =>
  forAll arbitrary (fun (k': nat)  =>
  forAll arbitrary (fun (v: nat) =>
  prop_InsertPost t k k' v))))
.

(*! QuickChick test_prop_InsertPost. *)

Definition test_prop_DeletePost    :=
  forAll gSized (fun (t: Tree)  =>
  forAll arbitrary (fun (k: nat)  =>
  forAll arbitrary (fun (k': nat) =>
  prop_DeletePost t k k')))
.

(*! QuickChick test_prop_DeletePost. *)

Definition test_prop_UnionPost   :=
  forAll gSized (fun (t: Tree)  =>
  forAll gSized (fun (t': Tree)  =>
  forAll arbitrary (fun (k: nat) =>
  prop_UnionPost t t' k)))
.

(*! QuickChick test_prop_UnionPost. *)

Definition test_prop_InsertModel   :=
  forAll gSized (fun (t: Tree)  =>
  forAll arbitrary (fun (k: nat)  =>
  forAll arbitrary (fun (v: nat) =>
  prop_InsertModel t k v)))
.

(*! QuickChick test_prop_InsertModel. *)

Definition test_prop_DeleteModel   :=
  forAll gSized (fun (t: Tree)  =>
  forAll arbitrary (fun (k: nat) =>
  prop_DeleteModel t k))
.

(*! QuickChick test_prop_DeleteModel. *)

Definition test_prop_UnionModel    :=
  forAll gSized (fun (t: Tree)  =>
  forAll gSized (fun (t': Tree) =>
  prop_UnionModel t t'))
.

(*! QuickChick test_prop_UnionModel. *)

Definition test_prop_InsertInsert    :=
  forAll gSized (fun (t: Tree)  =>
  forAll arbitrary (fun (k: nat)  =>
  forAll arbitrary (fun (k': nat)  =>
  forAll arbitrary (fun (v: nat)  =>
  forAll arbitrary (fun (v': nat) =>
  prop_InsertInsert t k k' v v')))))
.

(*! QuickChick test_prop_InsertInsert. *)

Definition test_prop_InsertDelete    :=
  forAll gSized (fun (t: Tree)  =>
  forAll arbitrary (fun (k: nat)  =>
  forAll arbitrary (fun (k': nat)  =>
  forAll arbitrary (fun (v: nat) =>
  prop_InsertDelete t k k' v))))
.

(*! QuickChick test_prop_InsertDelete. *)

Definition test_prop_InsertUnion   :=
  forAll gSized (fun (t: Tree)  =>
  forAll gSized (fun (t': Tree)  =>
  forAll arbitrary (fun (k: nat)  =>
  forAll arbitrary (fun (v: nat) =>
  prop_InsertUnion t t' k v))))
.

(*! QuickChick test_prop_InsertUnion. *)

Definition test_prop_DeleteInsert    :=
  forAll gSized (fun (t: Tree)  =>
  forAll arbitrary (fun (k: nat)  =>
  forAll arbitrary (fun (k': nat)  =>
  forAll arbitrary (fun (v': nat) =>
  prop_DeleteInsert t k k' v'))))
.

(*! QuickChick test_prop_DeleteInsert. *)

Definition test_prop_DeleteDelete    :=
  forAllShrink gSized shrink (fun (t: Tree)  =>
  forAllShrink arbitrary shrink (fun (k: nat)  =>
  forAllShrink arbitrary shrink (fun (k': nat) =>
  whenFail' (fun tt => show (t, k, k', delete k t, delete k' t, delete k (delete k' t), delete k' (delete k t)))
  (prop_DeleteDelete t k k'))))
.

(*! QuickChick test_prop_DeleteDelete. *)

Definition test_prop_DeleteUnion   :=
  forAll gSized (fun (t: Tree)  =>
  forAll gSized (fun (t': Tree)  =>
  forAll arbitrary (fun (k: nat) =>
  prop_DeleteUnion t t' k)))
.

(*! QuickChick test_prop_DeleteUnion. *)

Definition test_prop_UnionDeleteInsert   :=
  forAll gSized (fun (t :Tree)  =>
  forAll gSized (fun (t': Tree)  =>
  forAll arbitrary (fun (k: nat)  =>
  forAll arbitrary (fun (v: nat) =>
  prop_UnionDeleteInsert t t' k v))))
.

(*! QuickChick test_prop_UnionDeleteInsert. *)

Definition test_prop_UnionUnionIdem    :=
  forAll gSized (fun (t: Tree) =>
  prop_UnionUnionIdem t)
.

(*! QuickChick test_prop_UnionUnionIdem. *)

Definition test_prop_UnionUnionAssoc   :=
  forAll gSized (fun (t1: Tree)  =>
  forAll gSized (fun (t2: Tree)  =>
  forAll gSized (fun (t3: Tree) =>
  prop_UnionUnionAssoc t1 t2 t3)))
.

(*! QuickChick test_prop_UnionUnionAssoc. *)

"""
end
