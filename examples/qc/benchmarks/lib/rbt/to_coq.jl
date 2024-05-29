flatten = Iterators.flatten

function tocoq(c::Color.t)
    @match c [
        Red() -> "R",
        Black() -> "B",
    ]
end

function typebased_rbt_to_coq(p, adnodes_vals, io)
    expected_matchid(s) = s in ["leaf", "red", ["num$(n)" for n in twopowers(p.intwidth)]...]

    matchid_to_cases = Dict()
    for (name, val) in adnodes_vals
        matchid, case = split(name, "%%")
        @assert expected_matchid(matchid)
        case = "(" * join([tocoq(eval(Meta.parse(x))) for x in split(case, "%")], ", ") * ")"
        val = thousandths(val)
        push!(get!(matchid_to_cases, matchid, []), (case, val))
    end

    function dependent_to_code(sym)
        if sym == :stack_tail
            "($(join(["stack$(i)" for i in 1:p.stack_size], ", ")))"
        else
            string(sym)
        end
    end

    function mk_match(dependents, matchid)
        cases = matchid_to_cases[matchid]
        cases = sort(cases)
        if isnothing(dependents)
            "500"
        else
            "match ($(join(map(dependent_to_code, dependents), ","))) with 
$(join([" " ^ 9 * "| $(name) => $(w)" for (name, w) in cases], "\n"))
         | _ => 500
         end"
        end
    end

    stack_vars = ["(stack$(i) : nat)" for i in 1:p.stack_size]
    update_stack_vars(loc) = join(stack_vars[2:end], " ") * " $(loc)"

    """
Require Import ZArith.
From QuickChick Require Import QuickChick.
From ExtLib Require Import Monad.
From ExtLib.Data.Monads Require Import OptionMonad.
Import QcNotation.
Import MonadNotation.
From Coq Require Import List.
Import ListNotations.

From RBT Require Import Impl Spec.

Fixpoint manual_gen_tree (size : nat) (parent_color : Color) $(join(stack_vars, " ")) :=
    let weight_red := $(mk_match(p.red_dependents, "red")) in
    let weight_leaf := $(mk_match(p.leaf_dependents, "leaf")) in
    match size with
    | 0 => returnGen E
    | S size' =>
        freq [ (weight_leaf, returnGen E);
        (1000 - weight_leaf,
        bindGen (freq [ (weight_red, returnGen R); (1000-weight_red, returnGen B)])
          (fun p0 : Color =>
           bindGen (manual_gen_tree size' p0 $(update_stack_vars(10)))
             (fun p1 : Tree =>
$(
    join(
        ["         let weight_$(n) := $(mk_match(p.num_dependents, "num$(n)")) in
        bindGen (freq [ (weight_$(n), returnGen ($(n)%Z)); (1000-weight_$(n), returnGen 0%Z)])
        (fun n$(n) : Z =>  "
        for n in twopowers(p.intwidth)],
        "\n"
    )
)
let p2 := ($(join(["n$(n)" for n in twopowers(p.intwidth)], "+")))%Z in
                  bindGen arbitrary
                    (fun p3 : Z =>
                     bindGen (manual_gen_tree size' p0 $(update_stack_vars(11)))
                       (fun p4 : Tree => returnGen (T p0 p1 p2 p3 p4))
                      $(")" ^ p.intwidth) 
                       ))))]
         end.

#[global]
Instance genTree : GenSized (Tree) := 
  {| arbitrarySized n := manual_gen_tree $(p.size) B$(" 0" ^ p.stack_size) |}.

(* --------------------- Tests --------------------- *)

Definition test_prop_InsertValid :=  
    forAll arbitrary (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun v =>
        (prop_InsertValid t k v)))).

(*! QuickChick test_prop_InsertValid. *)

Definition test_prop_DeleteValid :=  
    forAll arbitrary (fun t =>    
    forAll arbitrary (fun k =>
        prop_DeleteValid t k)).

(*! QuickChick test_prop_DeleteValid. *)

Definition test_prop_InsertPost :=  
    forAll arbitrary (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun k' =>
     forAll arbitrary (fun v =>
        prop_InsertPost t k k' v)))).

(*! QuickChick test_prop_InsertPost. *)

Definition test_prop_DeletePost := 
    forAll arbitrary (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun k' =>
        prop_DeletePost t k k'))).

(*! QuickChick test_prop_DeletePost. *)
    
Definition test_prop_InsertModel :=  
    forAll arbitrary (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun v =>
        prop_InsertModel t k v))).

(*! QuickChick test_prop_InsertModel. *)
    
Definition test_prop_DeleteModel :=  
    forAll arbitrary (fun t =>    
    forAll arbitrary (fun k =>
            prop_DeleteModel t k)).

(*! QuickChick test_prop_DeleteModel. *)

Definition test_prop_InsertInsert :=  
    forAll arbitrary (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun k' =>
    forAll arbitrary (fun v =>
    forAll arbitrary (fun v' =>     
        prop_InsertInsert t k k' v v'))))).

(*! QuickChick test_prop_InsertInsert. *)
    
Definition test_prop_InsertDelete := 
    forAll arbitrary (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun k' =>
    forAll arbitrary (fun v =>
        prop_InsertDelete t k k' v)))).

(*! QuickChick test_prop_InsertDelete. *)
    
Definition test_prop_DeleteInsert := 
    forAll arbitrary (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun k' =>
    forAll arbitrary (fun v' =>
        prop_DeleteInsert t k k' v')))).

(*! QuickChick test_prop_DeleteInsert. *)
    
Definition test_prop_DeleteDelete :=  
    forAll arbitrary (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun k' =>
        prop_DeleteDelete t k k'))).

(*! QuickChick test_prop_DeleteDelete. *)

"""
end
