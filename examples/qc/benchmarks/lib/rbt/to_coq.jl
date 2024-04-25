flatten = Iterators.flatten

function tocoq(i::Integer)
    "$(i)"
end

function tocoq(c::Color.T)
    @match c [
        Red() -> "R",
        Black() -> "B",
    ]
end

function typebased_rbt_to_coq(p, adnodes_vals, io)
    leaf_cases = []
    red_cases = []
    num_cases = Dict()
    for (name, val) in adnodes_vals
        codeloc, case = split(name, "%%")
        case = "(" * join([tocoq(eval(Meta.parse(x))) for x in split(case, "%")], ", ") * ")"
        val = thousandths(val)
        if codeloc == "leaf"
            push!(leaf_cases, (case, val))
        elseif codeloc == "red"
            push!(red_cases, (case, val))
        elseif startswith(codeloc, "num")
            n = parse(Int, codeloc[4:end])
            push!(get!(num_cases, n, []), (case, val))
        else
            error()
        end
    end

    function mk_match(dependents, cases)
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
    
    red_match = mk_match(p.red_dependents, red_cases)
    leaf_match = mk_match(p.leaf_dependents, leaf_cases)

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

Definition manual_gen_tree :=
    fun s : nat =>
    (let
       fix arb_aux (size : nat) (parent_color : Color) (last_callsite : nat) : G Tree :=
         let weight_red := $(red_match) in
         let weight_leaf := $(leaf_match) in
$(
    join(
        ["         let weight_$(n) := $(mk_match(p.num_dependents, num_cases[n])) in"
        for n in twopowers(p.intwidth)],
        "\n"
    )
)
         match size with
         | 0 => returnGen E
         | S size' =>
             freq [ (weight_leaf, returnGen E);
             (1000 - weight_leaf,
             bindGen (freq [ (weight_red, returnGen R); (1000-weight_red, returnGen B)])
               (fun p0 : Color =>
                bindGen (arb_aux size' p0 20)
                  (fun p1 : Tree =>

$(
    join(
        [
"bindGen (freq [ (weight_$(n), returnGen ($(n)%Z)); (1000-weight_$(n), returnGen 0%Z)])
(fun n$(n) : Z => "
        for n in twopowers(p.intwidth)],
        "\n"
    )
)
                      bindGen arbitrary
                        (fun p3 : Z =>
let p2 := ($(join(["n$(n)" for n in twopowers(p.intwidth)], "+")))%Z in
                         bindGen (arb_aux size' p0 30)
                           (fun p4 : Tree => returnGen (T p0 p1 p2 p3 p4))
                          $(")" ^ p.intwidth) 
                           ))))]
         end in
     arb_aux) s.

#[global]
Instance genTree : GenSized (Tree) := 
  {| arbitrarySized n := manual_gen_tree $(p.size) B 10 |}.

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
