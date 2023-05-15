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
  intros n1 n2 m H.
  inversion H as [H12 | n H22 Hm].
  - split.
    + apply n_le_m__Sn_le_Sm. apply le_plus_l.
    + apply n_le_m__Sn_le_Sm. rewrite add_comm. apply le_plus_l.
  - rewrite <- Hm in H. apply Sn_le_Sm__n_le_m in H.
    apply plus_le in H. destruct H as [H1 H2].
    split.
    + apply n_le_m__Sn_le_Sm. apply H1.
    + apply n_le_m__Sn_le_Sm. apply H2.
Qed.

Theorem leb_complete : forall n m,
  n <=? m = true -> n <= m.
Proof.
  intros n m.
  generalize dependent m.
  induction n.
  - intros. apply O_le_n.
  - intros. destruct m.
    + discriminate.
    + simpl in H. apply IHn in H. apply n_le_m__Sn_le_Sm. apply H.
Qed.

Theorem leb_correct : forall n m,
  n <= m -> n <=? m = true.
Proof.
  intros n m.
  generalize dependent n.
  induction m.
  - intros. inversion H. reflexivity.
  - destruct n.
    + reflexivity.
    + intros. apply Sn_le_Sm__n_le_m in H. apply IHm in H.
      simpl. apply H.
Qed.

Theorem leb_iff : forall n m,
  n <=? m = true <-> n <= m.
Proof.
  split.
  - apply leb_complete.
  - apply leb_correct.
Qed.

Theorem leb_true_trans : forall n m o,
  n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
    intros n m o H1 H2.
    apply leb_complete in H1.
    apply leb_complete in H2.
    apply leb_correct.
    apply le_trans with m.
    - apply H1.
    - apply H2.
Qed.

Module R.
Inductive R : nat -> nat -> nat -> Prop :=
  | c_1 : R 0 0 0
  | c_2 m n o (H : R m n o ) : R (S m) n (S o)
  | c_3 m n o (H : R m n o ) : R m (S n) (S o)
  | c_4 m n o (H : R (S m) (S n) (S (S o))) : R m n o
  | c_5 m n o (H : R m n o ) : R n m o
  .

Example r_1_1_2 : R 1 1 2.
Proof.
  apply c_3. apply c_2. apply c_1.
Qed.

Example r_2_2_6 : R 2 2 6.
Proof. Abort.

Definition fR : nat -> nat -> nat :=
  plus.

Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
Proof.
  intros n m o.
  unfold fR.
  split.
  - intros H.
    induction H.
    + reflexivity.
    + simpl. f_equal. apply IHR.
    + rewrite <- plus_n_Sm. apply f_equal. apply IHR.
    + simpl in IHR. rewrite <- plus_n_Sm in IHR. 
      injection IHR. intros. apply H0.
    + rewrite add_comm. apply IHR.
  - intros H.
    rewrite <- H.
    destruct H.
    induction m.
    + induction n.
      * apply c_1.
      * simpl. apply c_2. apply IHn.
    + rewrite <- plus_n_Sm. apply c_3. apply IHm.
Qed.
End R.

Inductive subseq : list nat -> list nat -> Prop :=
  | subseq_0 (l : list nat): subseq [] l
  | subseq_1 (x : nat) (l1 l2 : list nat) (H: subseq l1 l2) : subseq (x :: l1) (x :: l2)
  | subseq_2 (x : nat) (l1 l2 : list nat) (H: subseq l1 l2) : subseq l1 (x :: l2)
  .

Theorem subseq_refl : forall (l : list nat), subseq l l.
Proof.
  intros l.
  induction l as [|h t IHt].
  - apply subseq_0.
  - apply subseq_1. apply IHt.
Qed.

Theorem subseq_app : forall (l1 l2 l3 : list nat),
  subseq l1 l2 -> subseq l1 (l2 ++ l3).
Proof.
  intros l1 l2 l3.
  intros H.
  induction H.
  - apply subseq_0.
  - simpl. apply subseq_1. apply IHsubseq.
  - simpl. apply subseq_2. apply IHsubseq.
Qed.

Theorem subseq_trans : forall (l1 l2 l3 : list nat),
  subseq l1 l2 -> subseq l2 l3 -> subseq l1 l3.
Proof.
  intros l1 l2 l3 H1 H2.
  generalize dependent l1.
  induction H2.
  - intros.
    assert (H11: l1 = []).
    { inversion H1. reflexivity. }
    rewrite H11. apply subseq_0.
  - intros. inversion H1.
    + apply subseq_0.
    + apply subseq_1. apply IHsubseq. apply H3.
    + apply subseq_2. rewrite <- H0. apply IHsubseq. rewrite H0. apply H3.
  - intros.
    apply subseq_2. apply IHsubseq. apply H1.
Qed.

Inductive R : nat -> list nat -> Prop :=
| c1                    : R 0     []
| c2 n l (H: R n     l) : R (S n) (n :: l)
| c3 n l (H: R (S n) l) : R n     l.

Example r_2_1_0: R 2 [1;0].
Proof.
  apply c2. apply c2. apply c1.
Qed.

Example r_1_2_1_0 : R 1 [1;2;1;0].
Proof.
  Abort.

Example r_6_3_2_1_0 : R 6 [3;2;1;0].
Proof.
  Abort.

Module bin1.
Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).
End bin1.

Module bin2.
Inductive bin : Type :=
  | Z : bin
  | B0 (n : bin) : bin
  | B1 (n : bin) : bin.
End bin2.

Module bin3.
Inductive bin : Type :=
  | Z : bin
  | B0 :  bin -> bin
  | B1 : bin -> bin.
End bin3.

Inductive reg_exp (T : Type) : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r_1 r_2 : reg_exp T)
  | Union (r_1 r_2 : reg_exp T)
  | Star (r : reg_exp T).

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

Reserved Notation "s =~ re" (at level 80).

Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
  | MEmpty : [] =~ EmptyStr
  | MChar x : [x] =~ (Char x)
  | MApp s_1 re_1 s_2 re_2
              (H_1 : s_1 =~ re_1)
              (H_2 : s_2 =~ re_2)
            : (s_1 ++ s_2) =~ (App re_1 re_2)
  | MUnionL s_1 re_1 re_2
              (H1 : s_1 =~ re_1)
            : s_1 =~ (Union re_1 re_2)
  | MUnionR re_1 s_2 re_2
              (H2 : s_2 =~ re_2)
            : s_2 =~ (Union re_1 re_2)
  | MStar0 re : [] =~ (Star re)
  | MStarApp s_1 s_2 re
              (H_1 : s_1 =~ re)
              (H_2 : s_2 =~ (Star re))
            : (s_1 ++ s_2) =~ (Star re)
  where "s =~ re" := (exp_match s re).

Example reg_exp_ex_1 : [1] =~ Char 1.
Proof. apply MChar. Qed.

Example reg_exp_ex_2 : [1;2] =~ App (Char 1) (Char 2).
Proof. 
  apply (MApp [1]).
  - apply MChar.
  - apply MChar.
Qed.

Example reg_exp_ex_2_0 : [1] ++ [2] =~ App (Char 1) (Char 2).
Proof.
  apply MApp.
  - apply MChar.
  - apply MChar.
Qed.

Example reg_exp_ex_2_1 : [1;2] =~ App (Char 1) (Char 2).
Proof. 
  apply (MApp [1] _ [2] _).
  - apply MChar.
  - apply MChar.
Qed.

Example reg_exp_ex3 : not ([1; 2] =~ Char 1).
Proof. intros H. inversion H. Qed.
  
Fixpoint reg_exp_of_list {T} (l: list T) :=
  match l with 
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl. apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.

Lemma MStar1 : forall T s (re : reg_exp T),
  s =~ re -> s =~ Star re.
Proof.
  intros.
  rewrite <- (app_nil_r _ s).
  apply MStarApp.
  - apply H.
  - apply MStar0.
Qed.

Lemma empty_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
  unfold not.
  intros. inversion H.
Qed.

Lemma MUnion' : forall T (s : list T) (re1 re2 : reg_exp T),
  s =~ re1 \/ s =~ re2 -> s =~ Union re1 re2.
Proof.
  intros.
  destruct H as [H | H].
  - apply MUnionL. apply H.
  - apply MUnionR. apply H.
Qed.

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
  (forall s, In s ss -> s =~ re) -> fold app ss [] =~ Star re.
Proof.
  intros.
  induction ss as [|hss tss IHss].
  - simpl. apply MStar0.
  - simpl. apply MStarApp.
    + apply H. simpl. left. reflexivity.
    + apply IHss. intros. apply H. simpl. right. apply H0.
Qed.

Fixpoint re_chars {T} (re : reg_exp T) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

Theorem in_re_match : forall T (s : list T) (re : reg_exp T) (x : T),
  s =~ re -> In x s -> In x (re_chars re).
Proof.
  intros T s re x HMatch Hin.
  induction HMatch
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  - (* MEmpty *)
    simpl in Hin. destruct Hin.
  - (* MChar *)
    simpl. simpl in Hin. apply Hin.
  - (* MApp *)
    simpl.
    rewrite In_app_iff.
    rewrite In_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      left. apply (IH1 Hin).
    + (* In x s2 *)
      right. apply (IH2 Hin).
  - (* MUnionL *)
    simpl. rewrite In_app_iff. left. apply (IH Hin).
  - (* MUininR *)
    simpl. rewrite In_app_iff. right. apply (IH Hin).
  - (* MStar0 *)
    destruct Hin.
  - (* MStarApp *)
    simpl.
    rewrite In_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      apply (IH1 Hin).
    + (* In x s2 *)
      apply (IH2 Hin).
Qed.

Fixpoint re_not_empty {T : Type} (re : reg_exp T) : bool :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char x => true
  | App re1 re2 => (re_not_empty re1) && (re_not_empty re2)
  | Union re1 re2 => (re_not_empty re1) || (re_not_empty re2)
  | Star re => true
  end.

Lemma re_not_empty_correct : forall T (re : reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  intros T re. split.
  - intros H. destruct H as [x H].
    induction H as
      [| x'
       | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
    + simpl. reflexivity.
    + simpl. reflexivity.
    + simpl. rewrite IH1. rewrite IH2. reflexivity.
    + simpl. rewrite IH. simpl. reflexivity.
    + simpl. rewrite IH. simpl. rewrite orb_true_iff. right. reflexivity.
    + simpl. reflexivity.
    + simpl. reflexivity.
  - intros H.
    induction re.
    + inversion H.
    + exists []. apply MEmpty.
    + exists [t]. apply MChar.
    + simpl in H. apply andb_true_iff in H. destruct H as [H1 H2].
      apply IHre1 in H1. apply IHre2 in H2.
      destruct H1 as [s1 H1]. destruct H2 as [s2 H2].
      exists (s1 ++ s2). apply MApp. apply H1. apply H2.
    + simpl in H. apply orb_true_iff in H. destruct H as [H | H].
      * apply IHre1 in H. destruct H as [s1 H]. exists s1. apply MUnionL. apply H.
      * apply IHre2 in H. destruct H as [s2 H]. exists s2. apply MUnionR. apply H.
    + simpl in H. exists []. apply MStar0.
Qed.

Lemma star_app_failed: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re -> s2 =~ Star re -> s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  (* inversion H1. *)
  generalize dependent s2.
  induction H1
  as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
      |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
      |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
  - (* MEmpty *)
    simpl. intros s2 H. apply H.
  - (* MChar. *) intros s2 H. simpl. (* Stuck... *)
Abort.

Lemma star_app_rewritten: forall T (s1 s2 : list T) (re re' : reg_exp T),
  re' = Star re ->
  s1 =~ re' ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  Abort.

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros R s1 s2 re H1.
  remember (Star re) as re'.
  generalize dependent s2.
  induction H1
  as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
      |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
      |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
  - (* MEmpty *) discriminate.
  - (* MChar *) discriminate.
  - (* MApp *) discriminate.
  - (* MUnionL *) discriminate.
  - (* MUnionR *) discriminate.
  - (* MStar0 *) 
    injection Heqre' as Heqre''. intros s H. simpl. apply H.
  - (* MStarApp *)
    injection Heqre' as Heqre''. intros s2 H1.
    rewrite app_assoc. apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * rewrite Heqre''. reflexivity.
      * apply H1.
Qed.

Lemma MStar'' : forall T (s : list T) (re : reg_exp T),
  s =~ Star re ->
  exists ss : list (list T),
    s = fold app ss []
    /\ forall s', In s' ss -> s' =~ re.
Proof.
  intros.
  remember (Star re) as re'.
  induction H
  as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
      |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
      |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - injection Heqre' as Heqre''.
    exists []. simpl. split.
    + reflexivity.
    + intros. inversion H.
  - injection Heqre' as Heqre''.
    destruct IH2 as [ss' [H1 H2]].
    + rewrite Heqre''. reflexivity.
    + exists (s1 :: ss'). split.
      * simpl. rewrite H1. reflexivity.
      * simpl. intros. destruct H as [H | H].
        -- rewrite <- Heqre''. rewrite <- H. apply Hmatch1.
        -- apply H2 in H. apply H.
Qed.

Module Pumping.

Fixpoint pumping_constant {T} (re : reg_exp T) : nat :=
  match re with
  | EmptySet => 1
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 => pumping_constant re1 + pumping_constant re2
  | Union re1 re2 => pumping_constant re1 + pumping_constant re2
  | Star r => pumping_constant r
  end.

Lemma pumping_contant_ge_1 : forall T (re : reg_exp T),
  pumping_constant re >= 1.
Proof.
  intros T re. induction re.
  - simpl. apply le_n.
  - simpl. apply le_n.
  - simpl. apply le_S. apply le_n.
  - simpl. apply le_trans with (n := pumping_constant re1).
    apply IHre1. apply le_plus_l.
  - simpl. apply le_trans with (n := pumping_constant re1).
    apply IHre1. apply le_plus_l.
  - simpl. apply IHre.
Qed.

Lemma pumping_constant_0_false : forall T (re : reg_exp T),
  pumping_constant re = 0 -> False.
Proof.
  intros T re H.
  assert (Hp1 : pumping_constant re >= 1).
  { apply pumping_contant_ge_1. }
  inversion Hp1 as [Hp1' | p Hp1' Hp1''].
  - rewrite H in Hp1'. discriminate Hp1'.
  - rewrite H in Hp1''. discriminate Hp1''.
Qed.

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

Lemma napp_plus: forall T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros T n m l.
  induction n as [|n IHn].
  - simpl. reflexivity.
  - simpl. rewrite IHn, app_assoc. reflexivity.
Qed.

Lemma napp_star : forall T m s1 s2 (re : reg_exp T),
  s1 =~ re -> s2 =~ Star re -> napp m s1 ++ s2 =~ Star re.
Proof.
  intros T m s1 s2 re Hs1 Hs2.
  induction m.
  - simpl. apply Hs2.
  - simpl. rewrite app_assoc. apply MStarApp.
    + apply Hs1.
    + apply IHm.
Qed.

Lemma week_pumping : forall T (re : reg_exp T) s,
  s =~ re -> pumping_constant re <= length s -> exists s1 s2 s3, s = s1 ++ s2 ++ s3 /\ s2 <> [] /\ forall m, s1 ++ napp m s2 ++ s3 =~ re.
Proof.
  intros T re s HMatch.
  induction HMatch
      as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - simpl. intros contra. inversion contra.
  - simpl. intros contra. apply Sn_le_Sm__n_le_m in contra. inversion contra.
  - intros H. simpl in H. rewrite app_length in H.
  apply add_le_cases in H. destruct H.
  + apply IH1 in H.
  destruct H as [s1' [s2' [s3' [Happ [Hne Hnapp]]]]].
  exists s1'. exists s2'. exists (s3' ++ s2).
  split. 
  
Abort.

Lemma  pumping : forall T (re : reg_exp T) s,
  s =~ re -> pumping_constant re <= length s ->
  exists s1 s2 s3, s = s1 ++ s2 ++ s3 /\ s2 <> [] /\ length s1 + length s2 <= pumping_constant re /\ forall m, s1 ++ napp m s2 ++ s3 =~ re.
Proof.
  intros T re s Hmatch.
  induction Hmatch
  as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
     | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
     | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
     simpl. intros contra. inversion contra.
  - (* MStr *)
    simpl. intros contra. apply Sn_le_Sm__n_le_m in contra. inversion contra.
    
   Admitted.
End Pumping.

Theorem filter_not_empty_In : forall n l,
  filter (fun x => n =? x) l <> [] -> In n l.
Proof.
  intros n l.
  induction l as [|m l' IHl'].
  - simpl. intros H. apply H. reflexivity.
  - simpl.  destruct (n =? m) eqn:H.
    + intros _. rewrite eqb_eq in H. rewrite H. left. reflexivity.
    + intros H'. right. apply IHl'. apply H'.
Qed.

Inductive reflect (P : Prop) : bool -> Prop :=
  | ReflectT (H : P) : reflect P true
  | ReflectF (H : ~ P) : reflect P false.

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  intros P b H. destruct b eqn:Eb.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. discriminate.
Qed.

Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros P b H.
  destruct H as [HP | HF].
  - split.
    + reflexivity.
    + intros. apply HP.
  - split.
    + intros. exfalso. apply HF. apply H.
    + intros. discriminate H.
Qed.

Lemma eqbP : forall n m, reflect (n = m) ( n =? m).
Proof.
  intros n m. apply iff_reflect. rewrite eqb_eq. reflexivity.
Qed.

Theorem filter_not_empty_In' : forall n l,
  filter (fun x => n =? x) l <> [] -> In n l.
Proof.
  intros n l.
  induction l as [|m l' IHl'].
  - simpl. intros H. apply H. reflexivity.
  - simpl. destruct (eqbP n m) as [H | H].
    + intros _. rewrite H. left. reflexivity.
    + intros H'. right. apply IHl'. apply H'.
Qed.

Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if n =? m then 1 else 0) + count n l'
  end.
  
Theorem eqbP_practice : forall n l,
  count n l = 0 -> ~(In n l).
Proof.
  intros n l Hcount. induction l as [| m l' IHl'].
  - intros contra. inversion contra.
  - simpl in Hcount. destruct (eqbP n m) as [H | H].
    + inversion Hcount.
    + intros contra. destruct contra as [Heq | HIn].
      * apply H. symmetry in Heq. apply Heq.
      * apply IHl'.
        -- simpl in Hcount. apply Hcount.
        -- apply HIn.
Qed.

Inductive nostutter { X : Type } : list X -> Prop :=
  | Nostutter_empty : nostutter []
  | Nostutter_one (x : X): nostutter [x]
  | Nostutter_n (x h: X) (l: list X) (H: nostutter (h :: l)) : x <> h -> nostutter (x :: (h :: l))
.

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
Proof.
  (* repeat constructor. discriminate. discriminate. discriminate. discriminate. discriminate. *)
  repeat constructor; apply eqb_neq; auto.
Qed.

Example test_nostutter_3: nostutter [5].
(* Proof. apply Nostutter_one. Qed. *)
Proof. constructor. Qed.

Example test_nostutter_4: not (nostutter [3;1;1;4]).
Proof.
  intro.
  repeat match goal with
    h: nostutter _ |- _ => inversion h; clear h; subst
  end.
  contradiction; auto.
Qed.

Inductive merge {X:Type} : list X -> list X -> list X -> Prop :=
  | merge_empty_1 (l1: list X) : merge l1 [] l1
  | merge_empty_2 (l2: list X) : merge [] l2 l2
  | merge_one_1 (h: X) (l1 l2 l3: list X) (H: merge l1 l2 l3) : merge (h :: l1) l2( h :: l3)
  | merge_one_2 (h: X) (l1 l2 l3: list X) (H: merge l1 l2 l3) : merge l1 (h :: l2) (h :: l3)
.

Theorem merge_filter : forall (X : Set) (test: X -> bool) (l l1 l2 : list X),
  merge l1 l2 l ->
  All (fun n => test n = true) l1 ->
  All (fun n => test n = false) l2 ->
  filter test l = l1.
Proof.
  intros X test l l1 l2 H H1 H2.
  induction H as [l1|l2|h l1 l2 l3 IHm|h l1 l2 l3 IHm].
  - induction l1.
    + simpl. reflexivity.
    + simpl in H1. destruct H1 as [Htest H1]. simpl.
      rewrite Htest. apply IHl1 in H1. rewrite H1. reflexivity.
  - induction l2.
    + simpl. reflexivity.
    + simpl in H2. destruct H2 as [Htest H2]. simpl.
      rewrite Htest. rewrite IHl2. 
      * reflexivity.
      * apply H2.
  - destruct H1 as [Htest H1]. simpl. rewrite Htest.
    apply IHIHm in H1.
    + rewrite H1. reflexivity.
    + apply H2.
  - destruct H2 as [Htest H2]. simpl. rewrite Htest.
    apply IHIHm in H1.
    + apply H1.
    + apply H2. 
Qed.

Theorem filter_subseq_length: forall (test: nat -> bool) (ls l : list nat),
  subseq ls l -> All (fun n => test n = true) ls -> length ls <= length (filter test l).
Proof.
  intros test ls l H1 H2.
  induction H1.
  - simpl. apply O_le_n.
  - simpl. destruct H2 as [Htest H2]. rewrite Htest. simpl.
    apply n_le_m__Sn_le_Sm. apply IHsubseq in H2. apply H2.
  - simpl. destruct (test x).
    + simpl. apply le_S. apply IHsubseq in H2. apply H2.
    + apply IHsubseq in H2. apply H2.
Qed.


Inductive pal {X:Type} : list X -> Prop :=
  | pal_empty : pal []
  | pal_one (x: X) : pal [x]
  | pal_many (x: X) (l: list X) (H: pal l) : pal (x :: l ++ [x])
.

Theorem pal_app_rev : forall (X:Type) (l : list X),
  pal (l ++ (rev l)).
Proof.
  intros X l.
  induction l as [|h l IHl].
  - simpl. apply pal_empty.
  - simpl. rewrite <- app_assoc. apply pal_many. apply IHl.
Qed.

Theorem pal_rev : forall (X:Type) (l: list X) , pal l -> l = rev l.
Proof.
  intros X l H.
  induction H as [|x|x l IHl].
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite rev_app_distr. rewrite <- IHIHl.
    simpl. reflexivity.
Qed.

Theorem palindrome_converse: forall {X: Type} (l: list X),
  l = rev l -> pal l.
Proof.
  intros X l H.
  induction l as [|h' l' IHl'].
  - apply pal_empty.
  - simpl in H.
  Abort.
  
Inductive disjoint {X : Type} : list X -> list X -> Prop :=
  | disjoint_empty (l : list X): disjoint [] l  
  | disjoint_one (x : X) (l1 l2 : list X) (P: ~ In x l2) (H : disjoint l1 l2) : disjoint (x :: l1) l2 
.

Inductive NoDup {X : Type} : list X -> Prop :=
  | nodup_empty : NoDup []  
  | nodup_more (x : X) (l : list X) (P: ~ In x l) (H: NoDup l) :  NoDup (x :: l)
.

Theorem no_dup_disjoint : forall (X : Type) (l1 l2 : list X),
NoDup l1 -> NoDup l2 -> disjoint l1 l2 -> NoDup (l1 ++ l2).
Proof.
  intros X l1 l2 H1 H2 H.
  induction H as [l'|x' l1' l2' P' H'].
  - simpl. apply H2.
  - simpl. apply nodup_more.
    + intros contra. apply In_app_iff in contra.
      destruct contra as [contra | contra].
      * inversion H1 as [|x'' l'' P'' H''].
        apply P''. apply contra.
      * apply P'. apply contra.
    + apply IHH'. inversion H1 as [|x'' l'' P'' H''].
      * apply H''.
      * apply H2.
Qed.

Lemma in_split : forall (X : Type) (x : X) (l : list X),
  In x l -> exists l1 l2, l = l1 ++ x :: l2.
Proof.
  intros X x l H.
  induction l as [|h l'].
  - inversion H.
  - simpl in H. destruct H as [H | H].
    + rewrite H. exists [], l'. simpl. reflexivity.
    + apply IHl' in H. destruct H as [l1' H]. destruct H as [l2' H].
      rewrite H.
      exists (h :: l1'), l2'.
      simpl. reflexivity.
Qed.

Inductive repeats {X:Type} : list X -> Prop :=
  | repeats_same (x : X) (l : list X) (P : In x l) : repeats(x :: l)
  | repeats_other  (x : X) (l : list X) (H : repeats(l)) : repeats (x :: l)
.

Example repeats_1 : repeats [1; 2; 3; 1].
Proof.
  apply repeats_same. simpl. right. right. left. reflexivity.
Qed.

Example repeats_2 : repeats [2; 1; 2; 3; 1].
Proof.
  apply repeats_other. apply repeats_1.
Qed.

Theorem pigeonhole_principle: excluded_middle ->
  forall (X:Type) (l1 l2:list X),
  (forall x, In x l1 -> In x l2) ->
  length l2 < length l1 ->
  repeats l1.
Proof.
  intros EM X l1. induction l1 as [|x l1' IHl1'].
  - simpl. intros. inversion H0.
  - intros. destruct (EM (In x l1')).
    + apply repeats_same. apply H1.
    + apply repeats_other.
      destruct (in_split X x l2) as [l0 [l2' H3]].
      * apply H. simpl. left. reflexivity.
      * apply IHl1' with (l0 ++ l2).
        -- intros. apply In_app_iff.
Abort.

Require Import Coq.Strings.Ascii.
Definition string := list ascii.

Lemma provable_equiv_true : forall (P : Prop), P -> (P <-> True).
Proof.
  intros. split.
  - intros. constructor.
  - intros. apply H.
Qed.

Lemma not_equiv_false : forall (P : Prop), ~ P -> (P <-> False).
Proof.
  intros.
  split.
  - apply H.
  - intros. destruct H0.
Qed.

Lemma null_matches_none : forall (s : string), (s =~ EmptySet) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

Lemma empty_matches_eps : forall (s : string), s =~ EmptyStr <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MEmpty.
Qed.

Lemma empty_nomatch_ne : forall (a : ascii) s, (a :: s =~ EmptyStr) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

Lemma char_nomatch_char :
  forall (a b : ascii) s, b <> a -> (b :: s =~ Char a <-> False).
Proof.
  intros.
  apply not_equiv_false.
  unfold not.
  intros.
  apply H.
  inversion H0.
  reflexivity.
Qed.

Lemma char_eps_suffix : forall (a : ascii) s, a :: s =~ Char a <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MChar.
Qed.

Lemma app_exists : forall (s : string) re0 re1,
  s =~ App re0 re1 <->
  exists s0 s1, s = s0 ++ s1 /\ s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros.
  split.
  - intros. inversion H. exists s_1, s_2. split.
    + reflexivity.
    + split. apply H_1. apply H_2.
  - intros [ s0 [ s1 [ Happ [ Hmat0 Hmat1 ] ] ] ].
    rewrite Happ. apply (MApp s0 _ s1 _ Hmat0 Hmat1).
Qed.

Lemma app_ne : forall (a : ascii) s re0 re1,
  a :: s =~ (App re0 re1) <->
  ([ ] =~ re0 /\ a :: s =~ re1) \/
  exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros.
  split.
  - intros H. inversion H.
    destruct s_1.
    + left. split.
      * apply H_1.
      * simpl. apply H_2.
    + right. exists s_1, s_2. split.
      *  inversion H1. reflexivity.
      * split. inversion H1. rewrite H4 in *. apply H_1. apply H_2.
  - intros [[H1 H2] | H].
    + replace (a :: s) with ([] ++ (a :: s)).
      * constructor.
        -- apply H1.
        -- apply H2.
      * reflexivity.
    + destruct H as [s0 [s1 [H1 [H2 H3]]]].
      rewrite H1.
      replace (a :: s0 ++ s1) with ((a :: s0) ++ s1).
      * constructor.
        -- apply H2.
        -- apply H3.
      * reflexivity.
Qed.
    
Lemma union_disj : forall (s : string) re0 re1,
  s =~ Union re0 re1 <-> s =~ re0 \/ s =~ re1.
Proof.
  intros. split.
  - intros. inversion H.
    + left. apply H2.
    + right. apply H1.
  - intros [ H | H ].
    + apply MUnionL. apply H.
    + apply MUnionR. apply H.
Qed.

Lemma star_ne : forall (a : ascii) s re,
  a :: s =~ Star re <->
  exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re /\ s1 =~ Star re.
Proof.
  intros a s re.
  split.
  - intros H. remember (Star re) as re'. remember (a::s) as s'.
    induction H.
    + inversion Heqs'.
    + inversion Heqre'.
    + inversion Heqre'.
    + inversion Heqre'.
    + inversion Heqre'.
    + inversion Heqs'.
    + destruct s_1 as [|h s_1].
      * inversion Heqre'. rewrite H2 in *.
        apply IHexp_match2 in Heqre'.
        destruct Heqre' as [s0 [s1 [Ha [Hb Hc]]]].
        exists s0, s1. split.
          apply Ha. split.
          apply Hb.
          apply Hc.
          apply Heqs'.
      * inversion Heqs'. rewrite H2 in *.
        inversion Heqre'. rewrite H4 in *.
        exists s_1, s_2. split.
        -- reflexivity.
        -- split.
           apply H. apply H0.
  - intros [s0 [s1 [H [H1 H2]]]].
    rewrite H. apply (MStarApp (a:: s0)).
    apply H1. apply H2.
Qed.


Definition refl_matches_eps m :=
  forall re : reg_exp ascii, reflect ([ ] =~ re) (m re).
        
Fixpoint match_eps (re: reg_exp ascii) : bool :=
match re with
| EmptySet => false
| EmptyStr => true
| Char x => false
| App re1 re2 => andb (match_eps re1) (match_eps re2)
| Union re1 re2 => orb (match_eps re1) (match_eps re2)
| Star re => true
end.

