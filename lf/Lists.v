From LF Require Export Induction.
Module NatList.

Inductive natprod : Type :=
  | pair (n_1 n_2 : nat).

Check (pair 3 5).

Definition fst (p : natprod) : nat :=
  match p with
  | pair x _ => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair _ y => y
  end.
  
Compute (fst (pair 3 5)).

Notation "( x , y )" := (pair x y).

Compute (fst (3, 5)).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x, _) => x
  end.

Definition snd' (p : natprod) : nat :=
  match p with
  | (_, y) => y
  end.
  
Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x, y) => (y, x)
  end.

Theorem  surjective_pairing': forall n m : nat,
  (n,m) = (fst (n,m), snd(n,m)). 
Proof.
  simpl. reflexivity.
Qed.

Theorem  surjective_pairing_stuck: forall p : natprod,
  p = (fst p, snd p).
Proof.
  simpl.
Abort.

Theorem  surjective_pairing: forall p : natprod,
  p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity.
Qed.

