
Require Import Arith Lia List String Floats.
Require Import ListSet.
Open Scope float_scope.
Open Scope nat_scope.
Import ListNotations.

Set Implicit Arguments.

Fixpoint genList (flip: float -> bool) (theta: nat -> float) (sz: nat) : list nat :=
  match sz with
    | O => nil
    | S sz' =>
      if flip (theta sz) then
        nil
      else
        cons 5 (genList flip theta sz')
  end.

Fixpoint genListLength (flip: float -> bool) (theta: nat -> float) (sz: nat) : nat :=
  match sz with
    | O => 0
    | S sz' =>
      if flip (theta sz) then
        0
      else
        1 + (genListLength flip theta sz')
  end.

Theorem genListLengthCorrect :
  forall flip theta sz,
    genListLength flip theta sz = Datatypes.length (genList flip theta sz).
Proof.
  intros flip theta sz.
  induction sz.
  - auto.
  - unfold genListLength, genList in *.
    destruct (flip (theta (S sz))).
    + auto.
    + simpl. auto.
Qed.

Inductive Tree :=
| Leaf : Tree
| Node : nat -> Tree -> Tree -> Tree.

Fixpoint genTree (flip: float -> bool) (theta: nat -> float) (sz : nat) : Tree :=
  match sz with
    | O => Leaf
    | S sz' =>
      if flip (theta sz) then
        Leaf
      else
        Node 5 (genTree flip theta sz') (genTree flip theta sz')
  end.

Fixpoint depth (tree: Tree) : nat :=
  match tree with
    | Leaf => 0
    | Node x l r => 1 + (max (depth l) (depth r))
end.

Fixpoint genTreeDepth (flip: float -> bool) (theta: nat -> float) (sz : nat) : nat :=
  match sz with
    | O => 0
    | S sz' =>
      if flip (theta sz) then
        0
      else
        1 + (max (genTreeDepth flip theta sz') (genTreeDepth flip theta sz'))
  end.

Theorem genTreeDepthCorrect :
  forall flip theta sz,
    genTreeDepth flip theta sz = depth (genTree flip theta sz).
Proof.
  intros flip theta sz.
  induction sz.
  - auto.
  - unfold genTreeDepth, genTree in *.
    destruct (flip (theta (S sz))).
    + auto.
    + simpl. auto.
Qed.
