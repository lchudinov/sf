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

Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).

Fail Inductive wrong_ev (n: nat) : Prop :=
  | wrong_ev_0 : wrong_ev 0
  | wrong_ev_SS (H : wrong_ev n) : wrong_ev (S (S n)).

Theorem ev_4 : ev 4.
  Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

Theorem ev_4' : ev 4.
  Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

Theorem ev_plus4: forall n, ev n -> ev (4 + n).
Proof.
 intros n. simpl. intros Hn. apply ev_SS. apply ev_SS. apply Hn. 
Qed.

Theorem ev_double : forall n,
  ev (double n).
Proof.
  intros n. induction n as [|n' IHn'].
  - simpl. apply ev_0.
  - simpl. apply ev_SS. apply IHn'.
Qed.

Theorem ev_inversion : forall (n : nat),
  ev n -> (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros n E. destruct E as [| n' E'] eqn:EE.
  - left. reflexivity.
  - right. exists n'. split.
    + reflexivity.
    + apply E'.
Qed.

Theorem evSS_ev: forall n, ev (S (S n)) -> ev n.
Proof.
  intros n H. apply ev_inversion in H. destruct H as [H0|H1].
  - discriminate H0.
  - destruct H1 as [n' [Hnm Hev]].
    injection Hnm as Heq. rewrite Heq. apply Hev.
Qed.

Theorem evSS_ev': forall n, ev (S (S n)) -> ev n.
Proof.
  intros n E. inversion E as [| n' E' Heq]. apply E'.
Qed.

Theorem one_not_even : ~ ev 1.
Proof.
  intros H. apply ev_inversion in H. destruct H as [ | [m [Hm _]]].
  - discriminate H.
  - discriminate Hm.
Qed.

Theorem one_not_even' : ~ ev 1.
Proof. intros H. inversion H. Qed.

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n H. inversion H. inversion H1. apply H3.
Qed.

Theorem ev5_nonsense : ev 5 -> 2 + 2 = 9.
Proof.
  intros H. inversion H. inversion H1. inversion H3.
Qed.

Theorem inversion_ex_1 : forall (n m o : nat),
  [n; m] = [o; o] -> [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity. Qed.
  
Theorem inversion_ex_2 : forall (n : nat),
  S n = O -> 2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

Lemma ev_Even_firsttry : forall n,
  ev n -> Even n.
Proof.
  unfold Even.
  intros n E. inversion E as [EQ' | n' E' EQ'].
  - exists 0. reflexivity.
  - assert (H: (exists k', n' = double k') -> (exists n0, S (S n') = double n0)).
    { intros [k' EQ'']. exists (S k'). simpl. rewrite EQ''. reflexivity. }
    apply H.
    generalize dependent E'.
    Abort.

Lemma ev_Even : forall n,
  ev n -> Even n.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - unfold Even. exists 0. reflexivity.
  - unfold Even in IH.
    destruct IH as [k Hk].
    rewrite Hk.
    unfold Even. exists (S k). simpl. reflexivity.
Qed.

Theorem ev_Even_iff : forall n,
  ev n <-> Even n.
Proof.
  split.
  - apply ev_Even.
  - unfold Even. intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

Theorem ev_sum: forall n m, ev n ->  ev m -> ev (n + m).
Proof.
  intros n m.
  intros H1 H2.
  induction H1 as [|n' H1' IH1].
  - simpl. apply H2.
  - simpl. apply ev_SS. apply IH1.
Qed.

Inductive ev' : nat -> Prop :=
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
  intros n.
  split.
  - intros H. induction H.
    + apply ev_0.
    + apply ev_SS. apply ev_0.
    + apply ev_sum. apply IHev'1. apply IHev'2.
  - intros H. induction H.
    + apply ev'_0.
    + rewrite <- plus_1_n. rewrite <- plus_n_Sm. rewrite <- plus_1_n.
      rewrite add_assoc. apply ev'_sum.
      * simpl. apply ev'_2.
      * apply IHev.
Qed.

Theorem ev_ev__ev : forall n m, ev (n+m) -> ev n -> ev m.
  (* Hint: There are two pieces of evidence you could attempt to induct upon
      here. If one doesn't work, try the other. *)
Proof.
  intros n m.
  intros H1 H2.
  induction H2.
  - rewrite plus_O_n in H1. apply H1.
  - simpl in H1. inversion H1 as [|n' evn' IH'].
    apply IHev. apply evn'.
Qed.

(*
  add_assoc: n + (m + p) = (n + m) + p.
*)

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros n m p H1 H2.
  assert (H: ev ((n+m) + (n+p))).
  {
    apply ev_sum. apply H1. apply H2.
  }
  Set Printing Parentheses.
  rewrite add_assoc in H.
  rewrite add_comm with (n + m) n in H.
  rewrite add_assoc with n n m in H.
  rewrite <- double_plus with n in H.
  rewrite <- add_assoc in H.
  apply ev_ev__ev with (double n) (m + p) in H.
  - apply H.
  - apply ev_double.
Qed.

Module Playground.

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : le n n
  | le_S (n m : nat) (H : le n m) : le n (S m).

Notation "n <= m" := (le n m).

Theorem test_l1_1: 3 <= 3.
Proof.
  apply le_n.
Qed.

Theorem test_le_2: 3 <= 6.
Proof.
  apply le_S. apply le_S. apply le_S. apply le_n.
Qed.

Theorem  test_le_3: (2 <= 1) -> 2 + 2 = 5.
Proof.
  intros H. inversion H. inversion H2.
Qed.

Definition lt (n m : nat) := le (S n) m.

Notation "m < n" := (lt m n).

End Playground.

Inductive total_relation : nat -> nat -> Prop :=
| total_On (n : nat) : total_relation 0 n
| total_Om (m : nat) : total_relation m 0
| total_Sn (n m : nat) (H : total_relation n m) : total_relation (S n) m
| total_Sm (n m : nat) (H : total_relation n m) : total_relation n (S m).

Theorem total_relation_is_total : forall n m, total_relation n m.
Proof.
  intros n m.
  induction n.
  - apply total_On.
  - apply total_Sn. apply IHn.
Qed.

Inductive empty_relation : nat -> nat -> Prop := .

Theorem empty_relation_is_empty : forall (n m: nat), ~ (empty_relation n m).
Proof.
  intros n m.
  unfold not.
  intros H.
  inversion H.
Qed.

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o H1 H2.
  induction H2 as [|o1 Ho IHo].
  - apply H1.
  - apply le_S. apply IHo.
Qed.

Theorem O_le_n : forall n, 0 <= n.
Proof.
  intros n. induction n.
  - apply le_n.
  - apply le_S. apply IHn.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m H.
  induction H as [|n' Hn' IHn'].
  - apply le_n.
  - apply le_S. apply IHn'.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m H.
  induction m.
  - inversion H as [H0 |n' H' IH'].
    + apply le_n.
    + inversion H'.
  - inversion H as [H0 |n' H' IH'].
    + apply le_n.
    + apply le_S in IHm.
      * apply IHm.
      * apply H'.
Qed.

Theorem lt_ge_cases : forall n m,
  n < m \/ n >= m.
Proof.
  intros n m.
  unfold lt. unfold ge.
  destruct m.
  - right. apply O_le_n.
  - induction n.
    + left. apply n_le_m__Sn_le_Sm. apply O_le_n.
    + destruct IHn as [H1 | H2].
      * destruct H1.
        -- right. apply le_n.
        -- left. apply n_le_m__Sn_le_Sm. apply H1.
      * right. apply le_S in H2. apply H2.
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros a b.
  induction a.
  - rewrite plus_O_n. apply O_le_n.
  - rewrite add_comm. rewrite <- plus_n_Sm. rewrite add_comm.
    apply n_le_m__Sn_le_Sm. apply IHa.
Qed. 

Theorem plus_le : forall n1 n2 m,
  n1 + n2 <= m -> n1 <= m /\ n2 <= m.
Proof.
  intros.
  induction H.
  - split.
    + apply le_plus_l.
    + rewrite add_comm. apply le_plus_l.
  - destruct IHle as [H1 H2].
    split.
    + apply le_S in H1. apply H1.
    + apply le_S in H2. apply H2.
Qed.

Theorem add_le_cases : forall n m p q,
  n + m <= p + q -> n <= p \/ m <= q.
Proof.
  induction n.
  - left. apply O_le_n.
  - intros. destruct p as [|p'] eqn:E.
    + right. apply plus_le in H. destruct H as [H1 H2].
      rewrite plus_O_n in H2. apply H2.
    + simpl in H.
      rewrite plus_n_Sm in H. rewrite plus_n_Sm in H.
      apply IHn in H. destruct H as [H | H].
      * apply n_le_m__Sn_le_Sm in H. left. apply H.
      * apply Sn_le_Sm__n_le_m in H. right. apply H.
Qed.
    
Theorem plus_le_compat_l : forall n m p, n <= m -> p + n <= p + m.
Proof.
  induction p.
  - rewrite plus_O_n. rewrite plus_O_n. intros H. apply H.
  - intros.
    rewrite add_comm with (S p) n.
    rewrite add_comm with (S p) m.
    rewrite <- plus_n_Sm with n p.
    rewrite <- plus_n_Sm with m p.
    apply n_le_m__Sn_le_Sm.
    rewrite add_comm with n p.
    rewrite add_comm with m p.
    apply IHp. apply H.
Qed.

Theorem plus_le_compat_r : forall n m p,
  n <= m -> n + p <= m + p.
Proof.
  induction p.
  - rewrite add_comm with n 0. rewrite add_comm with m 0. simpl.
    intros H. apply H.
  - rewrite <- plus_n_Sm with n p. rewrite <- plus_n_Sm with m p.
    intros H. apply n_le_m__Sn_le_Sm. apply IHp. apply H.
Qed.

Theorem le_plus_trans : forall n m p,
  n <= m -> n <= m + p.
Proof.
  induction p.
  - rewrite add_comm with m 0. simpl. intros H. apply H.
  - rewrite <- plus_n_Sm with m p.
    intros H. apply IHp in H. apply le_S in H. apply H.
Qed.

Theorem n_lt_m__n_le_m : forall n m,
  n < m -> n <= m.
Proof.
  unfold lt.
  intros. apply le_S in H. apply Sn_le_Sm__n_le_m in H. apply H.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m -> n1 < m /\ n2 < m.
Proof.
  unfold lt.
  split.
  Admitted.