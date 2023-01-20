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

Theorem plus_1_neg_0_firsttry : forall n : nat,
  ((n + 1) =? 0) = false.
Proof.
  intros n.
  simpl.
Abort.

Theorem plus_1_neg_0 : forall n : nat,
  ((n + 1) =? 0) = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + simpl. reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + simpl. reflexivity.
    + reflexivity.
Qed.

Theorem andb_commutative' : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  { destruct c eqn:Ec.
    { simpl. reflexivity. }
    { reflexivity. } }
  { destruct c eqn:Ec.
    { simpl. reflexivity. }
    { reflexivity. } }
Qed.

Theorem plus_1_neg_0' : forall n : nat,
  ((n + 1) =? 0) = false.
Proof.
  intros [| n].
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative'' : forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros [] [].
  - reflexivity.
  - intros H. rewrite <- H. reflexivity.
  - reflexivity.
  - intros H. rewrite <- H. reflexivity.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
  intros [].
  - reflexivity.
  - reflexivity.
Qed.

(* Exercise: 1 star, standard (identity_fn_applied_twice) *)
Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
Qed.

(* Exercise: 1 star, standard (negation_fn_applied_twice) *)
Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros.
  rewrite -> H.
  rewrite -> H.
  rewrite -> negb_involutive.
  reflexivity.
Qed.

(* Exercise: 3 stars, standard, optional (andb_eq_orb) *)
Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros [] [].
  - reflexivity.
  - simpl. intros H. rewrite -> H. reflexivity.
  - simpl. intros H. rewrite -> H. reflexivity.
  - reflexivity.
Qed.

Inductive bin : Type :=
  | Z
  | B_0 (n : bin)
  | B_1 (n : bin).

Fixpoint incr_with_carry (m: bin) (carry: bool) : bin :=
  match m, carry with
  | Z, _ => B_1 Z 
  | B_1 m', true => B_0 (incr_with_carry m' true)  
  | B_1 m', false => B_0 (incr_with_carry m' false)
  | B_0 m', _ => B_1 m'
  end.
  
Definition incr (m: bin) : bin :=
  incr_with_carry m false.
  
Compute (incr Z).
Compute (incr(incr Z)).
Compute (incr(incr(incr Z))).
Compute (incr(incr(incr(incr Z)))).
Compute (incr(incr(incr(incr(incr Z))))).
Compute (incr(incr(incr(incr(incr(incr Z)))))).

Example test_bin_incr1 : (incr (B_1 Z)) = B_0 (B_1 Z).
Proof. reflexivity. Qed.

Example test_bin_incr2 : (incr (B_0 (B_1 Z))) = B_1 (B_1 Z).
Proof. reflexivity. Qed.
 
Example test_bin_incr3 : (incr (B_1 (B_1 Z))) = B_0 (B_0 (B_1 Z)).
Proof. reflexivity. Qed.

Fixpoint bin_to_nat_rec (m:bin) (pos multiplier:nat) : nat :=
  match m, pos, multiplier with
  | Z, _, _ => 0
  | B_1 Z, _, _ => multiplier 
  | B_1 m', 0, 1 => 1 + (bin_to_nat_rec m' 1 2)
  | B_1 m', _, _ => multiplier + (bin_to_nat_rec m' (pos + 1) (multiplier * 2))
  | B_0 m', 0, 1 => (bin_to_nat_rec m' 1 2)
  | B_0 m', _, _ => (bin_to_nat_rec m' (pos + 1) (multiplier * 2))
  end.

Definition bin_to_nat (m:bin) := (bin_to_nat_rec m 0 1).

Definition one_bin := (B_1 Z).
Definition two_bin := (B_0 (B_1 Z)).
Definition three_bin := (B_1 (B_1 Z)).
Definition four_bin := (B_0 (B_0 (B_1 Z))).
Definition five_bin := (B_1 (B_0 (B_1 Z))).
Definition six_bin := (B_0 (B_1 (B_1 Z))).
Definition seven_bin := (B_1 (B_1 (B_1 Z))).
Definition eight_bin := (B_0 (B_0 (B_0 (B_1 Z)))).

Compute (bin_to_nat one_bin).
Compute (bin_to_nat two_bin).
Compute (bin_to_nat three_bin).
Compute (bin_to_nat four_bin).
Compute (bin_to_nat five_bin).
Compute (bin_to_nat six_bin).
Compute (bin_to_nat seven_bin).
Compute (bin_to_nat eight_bin).

Example test_bin_incr5 :
  bin_to_nat (incr (B_1 Z)) = 1 + bin_to_nat (B_1 Z).
Proof. cbn. reflexivity. Qed.

Example test_bin_incr6 :
  bin_to_nat (incr (incr (B_1 Z))) = 2 + bin_to_nat (B_1 Z).
Proof. cbv. reflexivity. Qed.

Example incr_seven: incr seven_bin = eight_bin.
Proof. reflexivity. Qed.

Example incr_seven_nat: bin_to_nat(incr seven_bin) = 8.
Proof. reflexivity. Qed.

Example incr_seven_twice_nat: bin_to_nat(incr (incr seven_bin)) = 9.
Proof. reflexivity. Qed.