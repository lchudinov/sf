Require Coq.extraction.Extraction.
Extraction Language Haskell.
From Coq Require Export String.


Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday (d: day) : day := 
  match d with
  | monday => thursday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Compute (next_weekday friday).
Compute (next_weekday (next_weekday saturday)).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = thursday.
Proof. simpl. reflexivity. Qed.

Extraction next_weekday.

Inductive bool : Type :=
  | true
  | false.

Definition negb (b:bool) : bool := 
match b with
| true => false
| false => true 
end.

Definition andb (a: bool) (b: bool) : bool := 
match a with
| true => b
| false => false
end .

Definition orb (a: bool) (b: bool) : bool := 
match a with
| true => true
| false => b
end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Compute negb(true).

Notation "a && b":= (andb a b).
Notation "a || b":= (orb a b).

Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

Definition negb' (b : bool) : bool := 
if b then false
else true.

Definition andb' (a: bool) (b: bool) : bool := 
if a then b
else false.

Definition orb' (a: bool) (b: bool) : bool := 
if a then true
else b.

Definition nandb (b1:bool) (b2:bool) : bool :=
  negb (andb b1 b2).
Example test_nandb1: (nandb true false) = true.
Proof. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  (andb b1 (andb b2 b3)).
Example test_andb31: (andb3 true true true) = true.
Proof. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. reflexivity. Qed.

Check true.
Check true : bool.
Check (negb true) : bool.
Check negb : bool -> bool.
Check andb.


Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).
  
Definition monochrome (c: color) : bool :=
  match c with
  | black => true
  | white => true
  | primary _ => false
end.

Definition isred (c: color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
end.

Module Playground.
  Definition b : rgb := blue.
End Playground.

Definition b : bool := true.

Check Playground.b : rgb.
Check b : bool.

Module TuplePlayground.
Inductive bit : Type :=
  | B0
  | B1.

Inductive nybble : Type :=
  | bits (b0 b1 b2 b3: bit).

Check (bits B1 B0 B1 B0).

Definition all_zero (nb: nybble) : bool :=
  match nb with
  | (bits B0 B0 B0 B0) => true
  | (bits _ _ _ _) => false
  end.

Check (all_zero (bits B1 B0 B1 B0)).
 
End TuplePlayground.

Module NatPlayground.

Inductive nat : Type :=
  | O
  | S (n : nat).
  
Inductive nat' : Type :=
  | stop
  | tick (n : nat').

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

End NatPlayground.

Check (S (S (S (S O)))).

Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Compute (minustwo 4).

Fixpoint even (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Definition odd (n : nat) : bool :=
  negb (even n).

Example test_odd1: odd 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_odd2: odd 4 = false.
Proof. simpl. reflexivity. Qed.

Module NatPlayground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Compute (plus 3 2).

Fixpoint mult (n m: nat) : nat :=
  match n with
  | O => O
  | S n' => plus m (mult n' m)
  end.

Example test_mul5by5: mult 5 5 = 25.
Proof. simpl. reflexivity. Qed.

Fixpoint minus (n m: nat): nat :=
  match n, m with
  | O, _ => O
  | S _, O => n
  | S n', S m' => minus n' m'
  end.

End NatPlayground2.

Notation "x + y" := (plus x y) (at level 50, left associativity) : nat_scope.
Notation "x - y" := (minus x y) (at level 50, left associativity) : nat_scope.
Notation "x * y" := (mult x y) (at level 40, left associativity) : nat_scope.

Check ((0 + 1) + 1) : nat.

Fixpoint factorial (n: nat) : nat :=
  match n with
  | O => 1
  | S O => 1
  | S n' => mult n (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Fixpoint eqb (n m: nat) : bool :=
  match n with
  | O => match m with
        | O => true
        | S _ => false
        end
  | S n' => match m with
        | O => false
        | S m' => eqb n' m'
        end
  end.
  
Fixpoint leb (n m: nat) : bool :=
  match n with
  | O => true
  | S n' => match m with
        | O => false
        | S m' => leb n' m'
        end
  end.

  Example test_leb1: leb 2 2 = true.
  Proof. simpl. reflexivity. Qed.
  Example test_leb2: leb 2 4 = true.
  Proof. simpl. reflexivity. Qed.
  Example test_leb3: leb 4 2 = false.
  Proof. simpl. reflexivity. Qed.
  
  Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
  Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
  Example test_leb3': (4 <=? 2) = false.
  Proof. simpl. reflexivity. Qed.
  
Definition ltb (n m : nat) : bool :=
  negb (m <=? n).
Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.
Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.

Theorem  plus_O_n :
  forall (n : nat), 0 + n = n.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Theorem  plus_O_n' :
  forall (n : nat), 0 + n = n.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem  plus_O_n'' :
  forall (n : nat), 0 + n = n.
Proof.
  intros m.
  reflexivity.
Qed.

Theorem  plus_1_n :
  forall (n : nat), 1 + n = S n.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem  mult_0_n :
  forall (n : nat), 0 * n = 0.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem plus_id_example : forall n m : nat,
  n = m -> n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity.
Qed.

Check mult_n_O.

Check mult_n_Sm.

Theorem mult_n_0_m_0 : forall p q : nat,
  (p * 0) + (q * 0) = 0.
Proof.
  intros p q.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity.
Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros m n o.
  intros H.
  rewrite -> H.
  intros I.
  rewrite -> I.
  reflexivity.
Qed.

Theorem mult_n_1 : forall p : nat,
  p * 1 = p.
Proof.
  intros p.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  simpl.
  reflexivity.
Qed.
