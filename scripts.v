Inductive bool : Type :=
| T
| F.

Definition negb (b : bool) : bool := 
  match b with (* Pattern matching syntax *)
  | T => F
  | F => T
  end.


Definition andb (b1 : bool) (b2 : bool) : bool :=
  match b1 with 
  | T => b2
  | F => F
  end.


Check andb : bool -> bool -> bool.

Definition orb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | T => T
  | F => b2
  end.

Compute (negb F). 

Compute (andb T F). 


Module NatDef.

Inductive nat : Type := (* Constructor                        *)
| O                     (* A nat can either be O or S of n    *)
| S (n : nat).          (* Only these two ways can form a nat *)


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

Theorem plus_O_l : forall n : nat, 0 + n = n. (* Goal *)
Proof.
  intros n. simpl. reflexivity. Qed. (* Tactics *)

Theorem plus_O_r : forall n : nat, n + 0 = n.
Proof.
  intros n. simpl. Fail reflexivity. Abort.

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
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Lemma plus_n_Sm : forall n m : nat, S (n + m) = n + S m.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

(* Provability is represented by evidence *)
(* A => B requires an evidence transformer *)
(* A proof is a program that manipulates evidence *)
(* Function that takes in 2 integers and outputs evidence of comm. *)
Theorem plus_comm : forall n m : nat, n + m = m + n.
Proof.
  intros n m. induction n as [| n' IHn'].
  - simpl. rewrite plus_O_r. reflexivity.
  - simpl. rewrite <- plus_n_Sm. rewrite IHn'. reflexivity.
Qed.

Check plus_comm.
Print plus_comm.

Theorem plus_id' : forall n m : nat, forall E: n = m, n + n = m + m.
Proof.
  intros n m E. rewrite -> E. reflexivity. Qed.
