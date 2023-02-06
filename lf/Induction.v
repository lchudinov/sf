From LF Require Export Basics. 

Example add_0_1 : forall n : nat,
  0 + n = n.
Proof. reflexivity. Qed.

Example add_0_r_firsttry : forall n : nat,
  n + 0 = n.
Proof.
  intros n.
  simpl.
Abort.


Example add_0_r_secondtry : forall n : nat,
  n + 0 = n.
Proof.
  intros n. destruct n as [|n'] eqn:E.
  - reflexivity.
  - simpl.
Abort.

Theorem add_0_r : forall n : nat,
  n + 0 = n.
Proof.
  intros n. induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem minus_n_n: forall n,
  n - n = 0.
Proof.
  intros n. induction n as [| k].
   - reflexivity.
   - simpl. rewrite -> IHk. reflexivity.
Qed.

Theorem plus_n_Sm: forall n m : nat,
  S (n + m) = n + S m.
Proof.
  intros n m. induction n as [| n'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem add_comm : forall a b : nat,
  a + b = b + a.
Proof.
  intros a b. induction a as [| a'].
  - simpl. rewrite add_0_r. reflexivity.
  - simpl. rewrite IHa'. rewrite plus_n_Sm. reflexivity.
Qed.

Theorem mult_0_plus' : forall n m : nat,
  (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  assert (H: n + 0 + 0 = n).
  { 
    (*Set Printing Parentheses.*)
    rewrite add_comm.
    simpl.
    rewrite add_comm.
    simpl.
    reflexivity.
  }
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* Set Printing Parentheses. *)
  rewrite add_comm.
Abort.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite add_comm. reflexivity. }
  rewrite H.
  reflexivity. 
Qed.

Theorem mul_0_r : forall n : nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [|n'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .
Proof.
  intros n. induction n as [|n'].
  - reflexivity.
  - simpl. rewrite IHn'. rewrite plus_n_Sm. reflexivity.
Qed.

Theorem eqb_refl : forall n : nat,
  (n =? n) = true.
Proof.
  intros n. induction n as [|n'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof.
  intros n. induction n as [|n'].
  - simpl. reflexivity.
  - rewrite -> IHn'. rewrite negb_involutive. simpl. reflexivity.
Qed.

Theorem add_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [|n' IHn']. reflexivity.
  simpl. rewrite IHn'. reflexivity.
Qed.

Theorem add_assoc'' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [|n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl. rewrite IHn'. reflexivity.
(** - _Theorem_: For any [n], [m] and [p],
      n + (m + p) = (n + m) + p.
    _Proof_: By induction on [n].
    - First, suppose [n = 0]. We must show that
        0 + (m + p) = (0 + m) + p.
      This follows directly from the definition of [+].
    - Next, suppose [n = S n'], where
      n' + (m + p) = (n' + m) + p.
    We must now show that  
      (S n') + (m + p) = ((S n') + m) + p.
    By the definition of [+], this follows from
      S (n' + (m + p)) = S((n' + m) + p),
    which is immediate from the induction hypothesis. _Qed_.
*)
Qed.

Theorem add_comm' : forall a b : nat,
  a + b = b + a.
Proof.
  intros a b. induction a as [| a'].
  - simpl. rewrite add_0_r. reflexivity.
  - simpl. rewrite IHa'. rewrite plus_n_Sm. reflexivity.
(** - _Theorem_: For any [a] and [b],
      a + b = b + a.
    _Proof_: By induction on [a].
    - First, suppose [a = 0]. We must show that
        0 + b = b + 0.
      This follows directly from the definition of [+].
    - Next, suppose [a = S a'], where
      a' + b = b + 'a.
    We must now show that  
      (S a') + b = b + (S a').
    By the definition of [+], this follows from
      S (a' + b) = S (b + a').
    which is immediate from the induction hypothesis. _Qed_.
*)
Qed.

Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite add_assoc.
  assert (H1: m + (n + p) = m + n + p).
  { rewrite add_assoc. reflexivity. }
  assert (H2: n + m = m + n).
  { rewrite add_comm. reflexivity. }
  rewrite H1.
  rewrite <- H2.
  reflexivity.
Qed.
Theorem  mul_n_0: forall n : nat,
  n * 0 = 0.
Proof.
  induction n.
  - reflexivity.
  Admitted.

Lemma n_k_1 : forall n k : nat,
  n * (1 + k) = n + n * k.
Proof.
  intros n k.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite add_assoc.
    assert (n' + k = k + n').
    { rewrite add_comm. reflexivity. }
    rewrite H.
    rewrite <- add_assoc.
    rewrite <- IHn'.
    Set Printing Parentheses.
    assert (1 + k = S k).
    { rewrite plus_1_n. reflexivity. }
    rewrite H0.
    reflexivity.
  Qed.
    
Theorem mul_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros n m.
  induction n as [|k IHk'].
  - simpl.
    assert (m * 0 = 0).
    induction m.
    -- rewrite mul_0_r. reflexivity.
    -- simpl. rewrite IHm. reflexivity.
    -- rewrite H. reflexivity.
  - assert (m * (S k) = m * (1 + k)).
    { rewrite <- plus_1_n. reflexivity. }
    rewrite H.
    rewrite n_k_1.
    rewrite <- IHk'.
    rewrite <- plus_1_n.
    simpl.
    reflexivity.
Qed.

Check leb.

Lemma leb_a : forall a,
  leb a a = true.
Proof.
  intros [].
  - reflexivity.
  - induction n.
    -- simpl. reflexivity.
    -- simpl. rewrite <- IHn. simpl. reflexivity.
Qed.

Lemma leb_a_S_a : forall a,
  leb a (S a) = true.
Proof.
  intros a.
  induction a.
  - simpl. reflexivity.
  - simpl. rewrite <- IHa. reflexivity.
Qed.

Lemma leb_a_b : forall a b,
  leb a (a + b) = true.
Proof.
  intros a b.
  induction b.
  - rewrite add_comm. simpl. rewrite leb_a. reflexivity.
  - rewrite <- plus_n_Sm.
    destruct b.
    -- rewrite add_comm. simpl. rewrite leb_a_S_a. reflexivity.
    -- rewrite <- IHb.
Abort.

Theorem plus_leb_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  intros n m p.
  intros H.
  induction p as [|p' IHp'].
  - simpl. rewrite H. reflexivity.
  - simpl. rewrite IHp'. reflexivity.
Qed.


(* guess: destruction *)
(* reality: induction *)
Theorem leb_refl : forall n:nat,
  (n <=? n) = true.
Proof.
  intros [].
  - reflexivity.
  - induction n.
    -- reflexivity.
    -- rewrite <- IHn.
       simpl. reflexivity.
Qed. 

(* guess: destruction *)
(* reality: induction *)
Theorem zero_neqb_S : forall n:nat,
  0 =? (S n) = false.
Proof.
  induction n as [|n' IHn'].
  - reflexivity.
  - rewrite <- IHn'. simpl. reflexivity.
Qed.
(* guess: destruction *)
(* reality: destruction *)
Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intros [].
  - reflexivity.
  - reflexivity.
Qed.

(* guess: destruction *)
(* reality: destruction *)
Theorem S_neqb_0 : forall n:nat,
(S n) =? 0 = false.
Proof.
  intros [].
  - reflexivity.
  - reflexivity.
  Qed.
  
(* guess: induction *)
Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite <- add_comm. simpl. reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p.
  induction p as [|p' IHp'].
  - rewrite mul_0_r. rewrite mul_0_r. rewrite mul_0_r. reflexivity.
  - assert (Hs1: n * S p' = n * p' + n).
    { rewrite mul_comm. simpl. rewrite mul_comm. rewrite add_comm. reflexivity. }
    assert (Hs2: m * S p' = m * p' + m).
    { rewrite mul_comm. simpl. rewrite mul_comm. rewrite add_comm. reflexivity. }
    assert (Hs3: (n + m) * S p' = (n + m) * p' + (n + m)).
    { rewrite mul_comm. simpl. rewrite mul_comm. rewrite add_comm. reflexivity. }
    rewrite Hs1. rewrite Hs2. rewrite Hs3.
    rewrite IHp'. rewrite add_assoc. rewrite add_assoc.
    assert (Ha: (m * p') + (n * p') = (n * p') + (m * p')).
    { rewrite add_comm. reflexivity. }
    assert (Hf: ((n * p') + n) + (m * p') = (n * p') + (m * p') + n).
    { rewrite add_comm. rewrite add_assoc. rewrite Ha. reflexivity. }
    rewrite Hf.
    reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'.
    rewrite mult_plus_distr_r.
    reflexivity.
Qed.

Theorem add_shuffle3' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite add_assoc.
  replace (n + m) with (m + n).
  - rewrite add_assoc. reflexivity.
  - rewrite add_comm. reflexivity.
Qed.

Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
  intros b.
  induction b as [|b' |b'].
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite IHb'. rewrite plus_1_n. rewrite plus_n_Sm. reflexivity.
Qed.

Fixpoint nat_to_bin (n:nat) : bin :=
  match n with
    | O => Z
    | S n' => incr (nat_to_bin n')
  end.

  
Theorem nat_bin_nat : forall n,
  bin_to_nat (nat_to_bin n) = n.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite bin_to_nat_pres_incr. rewrite IHn'. reflexivity.
Qed.

Theorem bin_nat_bin_fails : forall b, nat_to_bin (bin_to_nat b) = b.
Abort.

Lemma double_incr : forall n : nat,
  double (S n) = S (S (double n)).
Proof.
  intros n.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

Definition double_bin (b:bin) : bin :=
  match b with
  | Z => Z
  | n => B_0 n
  end.

Example double_bin_zero : double_bin Z = Z.
Proof.
  simpl. reflexivity.
Qed.

Lemma double_incr_bin : forall b,
  double_bin (incr b) = incr (incr (double_bin b)).
Proof.
  intros b.
  induction b as [|b' |b' IHb'].
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem bin_nat_bin_fails : forall b, nat_to_bin (bin_to_nat b) = b.
Abort.

Fixpoint normalize (b:bin) : bin :=
  match b with
  | Z => Z
  | B_0 b' => double_bin (normalize b')
  | B_1 b' => incr (double_bin (normalize b'))
end.

Example test_normalize0_1 : normalize Z = Z.
Proof. reflexivity. Qed.

Example test_normalize0_2 : normalize (B_0 Z) = Z.
Proof. reflexivity. Qed.

Example test_normalize0_3 : normalize (B_0 (B_0 Z)) = Z.
Proof. reflexivity. Qed.

Example test_normalize0_4 : normalize (B_0 (B_0 (B_0 Z))) = Z.
Proof. reflexivity. Qed.

Example test_normalize1 : bin_to_nat (normalize (B_1 Z)) = 1.
Proof. reflexivity. Qed.

Example test_normalize2 : bin_to_nat (normalize (B_0 (B_1 Z))) = 2.
Proof. reflexivity. Qed.

Example test_normalize3 : bin_to_nat (normalize (B_1 (B_1 Z))) = 3.
Proof. reflexivity. Qed.

Example test_normalize4 : bin_to_nat (normalize (B_0 (B_0 (B_1 Z)))) = 4.
Proof. reflexivity. Qed.

Theorem bin_nat_bin : forall b, nat_to_bin (bin_to_nat b) = normalize b.
Proof.
Abort.

Lemma nat_to_bin_double : forall n : nat,
  nat_to_bin(double n) = double_bin(nat_to_bin n).
Proof.
  intros n.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite -> double_incr_bin. rewrite <- IHn. reflexivity.
Qed.

Compute bin_to_nat (normalize (B_0 (B_1 Z))).
Compute bin_to_nat (normalize (B_1 (B_1 Z))).

Theorem bin_nat_bin : forall b,
  nat_to_bin (bin_to_nat b) = normalize b.
Proof.
  intros b.
  induction b as [|b' |b'].
  - simpl. reflexivity.
  - simpl. rewrite <- IHb'.
    destruct (bin_to_nat b').
    -- reflexivity.
    -- rewrite <- double_plus. rewrite -> nat_to_bin_double. reflexivity.
  - simpl. rewrite <- IHb'. rewrite <- double_plus. rewrite <- nat_to_bin_double. reflexivity.
Qed.
   