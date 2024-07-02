Inductive bool : Type :=
| T
| F.

(* Bool is a type *)

Definition negb (b : bool) : bool := 
  match b with 
  | T => F
  | F => T
  end.

(* fn from bool to bool, pattern matching *)

Definition andb (b1 : bool) (b2 : bool) : bool :=
  match b1 with 
  | T => b2
  | F => F
  end.

Definition orb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | T => T
  | F => b2
  end.


Compute (negb F). 

Compute (andb T F). 

Check andb : bool -> bool -> bool.

(* Takes 2 bool output 1 *)

Module NatDef.

Inductive nat : Type := 
| O 
| S (n : nat).

(* O not 0 *)

(* 
    the constructor expression O belongs to the set nat;
    if n is a constructor expression belonging to the set nat, then S n is also a constructor expression belonging to the set nat; and
    constructor expressions formed in these two ways are the only ones belonging to the set nat.
 *)

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

End NatDef.

Fixpoint even (n: nat) : bool :=
  match n with 
  | O => T
  | S O => F
  | S (S n') => even n'
  end.

Definition odd (n: nat) : bool :=
  negb (even n).

Fixpoint plus (n m: nat) : nat :=
  match n with 
  | O => m
  | S n' => S (plus n' m)
  end.

Compute (plus 3 1).

(* S (plus 2 1) => S (S (plus 1 1)) => S (S (S (plus 0 1))) => S (S (S (S O)))*)

Fixpoint minus (n m: nat) : nat :=
  match n, m with
  | O, _ => O
  | _, O => n
  | S n', S m' => minus n' m'
  end.

Compute (minus 3 1).

(* Talk about tactics and goals *)

Theorem plus_O_l : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem plus_O_r : forall n : nat, n + 0 = n.
Proof.
  intros n. simpl. Fail reflexivity. Abort.

(* Talk about the context *)

Theorem plus_id : forall n m : nat, n = m -> n + n = m + m.
Proof.
  intros n m H. rewrite -> H. reflexivity. Qed.

Theorem and_comm : forall a b, andb a b = andb b a.
intros a b. destruct a.
  - destruct b.
    + simpl. reflexivity.
    + simpl. reflexivity.
  - destruct b.
    + simpl. reflexivity.
    + simpl. reflexivity.
Qed.

Theorem plus_O_r : forall n : nat, n + 0 = n.
Proof. 
  intros n. destruct n as [| n'].
  - reflexivity.
  - Abort.

Theorem plus_O_r : forall n : nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.
