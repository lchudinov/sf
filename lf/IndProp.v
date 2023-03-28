Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Logic.
From Coq Require Import Lia.

Fixpoint div2 (n : nat) :=
  match n with
  | 0 => 0
  | 1 => 0
  | S (S n) => S (div2 n)
  end.

Definition  f (n : nat) := 
  if even n then div2 n
  else (3 * n) + 1.

Fail Fixpoint reaches_1_in (n : nat) :=
  if n =? 1 then 0
  else 1 + reaches_1_in (f n).

Inductive reaches_1 : nat -> Prop :=
  | term_done : reaches_1 1
  | term_more (n : nat) : reaches_1 (f n) -> reaches_1 n.
  
Conjecture collatz : forall n, reaches_1 n.

Module LePlayground.

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : le n n
  | le_S (n m : nat) : le n m -> le n (S m).
  
End LePlayground.

Inductive clos_trans {X : Type} (R: X -> X -> Prop) : X -> X -> Prop :=
  | t_step (x y: X) : R x y -> clos_trans R x y
  | t_trans (x y z : X) : clos_trans R x y -> clos_trans R y z -> clos_trans R x z.

Inductive clos_trans_refl_sym {X : Type} (R: X -> X -> Prop) : X -> X -> Prop :=
  | t_step_rs (x y: X) : R x y -> clos_trans_refl_sym R x y
  | t_refl (x : X) : clos_trans_refl_sym R x x
  | t_sym (x y : X) : clos_trans_refl_sym R x y -> clos_trans_refl_sym R y x
  | t_trans_rs (x y z : X) : clos_trans_refl_sym R x y -> clos_trans_refl_sym R y z -> clos_trans_refl_sym R x z.
  
Inductive Perm3 {X : Type} : list X -> list X -> Prop :=
  | perm3_swap12 (a b c : X) : Perm3 [a;b;c] [b;a;c]
  | perm3_swap23 (a b c : X) : Perm3 [a;b;c] [a;c;b]
  | perm3_trans (l_1 l_2 l_3 : list X) : Perm3 l_1 l_2 -> Perm3 l_2 l_3 -> Perm3 l_1 l_3.

  

