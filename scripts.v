From Coq Require Export Bool.Bool.
From Coq Require Export Arith.Arith.
From Coq Require Export Arith.PeanoNat.
From Coq Require Export Arith.EqNat.
From Coq Require Export Lists.List.
From Coq Require Export Permutation.
Import ListNotations.

From Coq Require Export Extraction.


Module NatDef.

Inductive nat : Type := (* Constructor *)
| O                     
| S (n : nat).          



End NatDef.

Compute S (S O).


Fixpoint plus (n m: nat) : nat :=
  match n with 
  | O => m
  | S n' => S (plus n' m)
  end.

Compute (plus 3 1).

(* S (plus 2 1) => S (S (plus 1 1)) => S (S (S (plus 0 1))) => S (S (S (S O)))*)

Theorem plus_O_l : forall n : nat, 0 + n = n. (* Goal *)
Proof.
  intros n. simpl. reflexivity. Qed. (* Tactics *)

Theorem plus_O_r : forall n : nat, n + 0 = n.
Proof.
  intros n. simpl. Fail reflexivity. Abort.

Theorem plus_O_r : forall n : nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat, S (n + m) = n + S m.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat, n + m = m + n.
Proof.
  intros n m. induction n as [| n' IHn'].
  - simpl. rewrite -> plus_O_r. reflexivity.
  - simpl. rewrite <- plus_n_Sm. rewrite -> IHn'. reflexivity.
Qed.







Fixpoint insert (i : nat) (l : list nat) :=
  match l with
  | nil => [i]
  | h :: t => if i <=? h then i :: h :: t else h :: insert i t
  end.

(* Insertion Sort! *)
Fixpoint sort (l : list nat) : list nat :=
  match l with
  | nil => nil
  | h :: t => insert h (sort t)
  end.

Example sort_pi :
  sort [3;1;4;1;5;9;2;6;5;3;5]
  = [1;1;2;3;3;4;5;5;5;6;9].
Proof.
  reflexivity. Qed.


(* Define sorted predicate *)
Inductive sorted : list nat -> Prop :=
| sorted_nil : sorted []
| sorted_1 : forall x, sorted [x]
| sorted_cons : forall x y: nat, forall l: list nat, x <= y -> sorted (y :: l) -> sorted (x :: y :: l).














Lemma insert_sorted:
  forall (a : nat) (l : list nat), sorted l -> sorted (insert a l).
Proof. Admitted.

Check insert_sorted.

Theorem sort_sorted: forall l, sorted (sort l).
Proof. induction l as [| h t IHl].
  - simpl. constructor.
  - simpl. apply insert_sorted. apply IHl. Qed.

Extraction Language Haskell.
Recursive Extraction sort.

Extraction Language Scheme.
Recursive Extraction sort.