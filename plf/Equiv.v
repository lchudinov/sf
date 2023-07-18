Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Logic.FunctionalExtensionality.
From PLF Require Export Imp.
Set Default Goal Selector "!".

Definition aequiv (a1 a2 : aexp) : Prop := 
  forall (st : state), aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop := 
  forall (st : state), beval st b1 = beval st b2.

Theorem  aequiv_example :
  aequiv
    <{ X - X }>
    <{ 0 }>.
Proof.
  intros st. simpl. lia.  
Qed.

Theorem bequiv_example:
  bequiv
    <{ X - X = 0}>
    <{ true }>.
Proof.
  intros st. unfold beval. rewrite aequiv_example. reflexivity.
Qed.

Definition cequiv (c1 c2 : com) : Prop := 
  forall (st st' : state),
  (st =[ c1 ]=> st') <-> (st =[ c2 ]=> st').

Definition refines (c1 c2 : com) : Prop := 
  forall (st st' : state),
  (st =[ c1 ]=> st') -> (st =[ c2 ]=> st').
  
Theorem skip_left : forall c,
  cequiv
    <{ skip; c }>
    c .
Proof.
  intros c st st'.
  split; intros H.
  - inversion H. subst.
    inversion H2. subst.
    assumption.
  - apply E_Seq with st.
    + apply E_Skip.
    + assumption.
Qed.

Theorem skip_right : forall c,
  cequiv
    <{ c; skip }>
    c .
Proof.
  intros c st st'.
  split; intros H.
  - inversion H. inversion H5. subst. assumption.
  - apply E_Seq with st'.
    + assumption.
    + apply E_Skip.
Qed.

Theorem if_true : forall b c1 c2,
  bequiv b <{ true }> ->
  cequiv <{ if b then c1 else c2 end }>
  c1.
Proof.
  intros b c1 c2 Hb.
  split; intros.
  - inversion H; subst.
    + assumption.
    + unfold bequiv in Hb. simpl in Hb.
      rewrite Hb in H5.
      discriminate.
  - apply E_IfTrue; try assumption.
    unfold bequiv in Hb. simpl in Hb. apply Hb.
Qed.

Theorem if_false : forall b c1 c2,
  bequiv b <{ false }> ->
  cequiv <{ if b then c1 else c2 end }>
  c2.
Proof.
  intros b c1 c2 Hb.
  split; intros.
  - inversion H; subst; unfold bequiv in Hb; simpl in Hb; rewrite Hb in H5.
    + discriminate.
    + assumption.
  - apply E_IfFalse; try assumption.
    unfold bequiv in Hb. simpl in Hb. apply Hb.
Qed.

Theorem swap_if_branches : forall b c1 c2,
  cequiv
    <{ if b then c1 else c2 end }>
    <{ if ~ b then c2 else c1 end }>.
Proof.
  unfold cequiv. intros.
  split; intros.
  - inversion H; subst.
    + apply E_IfFalse.
      * simpl. rewrite H5. reflexivity.
      * assumption.
    + apply E_IfTrue.
      * simpl. rewrite H5. reflexivity.
      * assumption.
  - inversion H; subst.
    + apply E_IfFalse.
      * simpl in H5. rewrite negb_true_iff in H5. assumption.
      * simpl in H5. rewrite negb_true_iff in H5. assumption.
    + apply E_IfTrue.
      * simpl in H5. rewrite negb_false_iff in H5. assumption.
      * assumption.
Qed.

Theorem while_false : forall b c,
  bequiv b <{false}> ->
  cequiv
    <{ while b do c end }>
    <{ skip }>.
Proof.
  intros b c Hb. split; intros H.
  - inversion H; subst.
    + apply E_Skip.
    + rewrite Hb in H2. discriminate.
  - inversion H; subst.
    + apply E_WhileFalse. apply Hb.
Qed.

Lemma while_true_nonterm : forall b c st st',
  bequiv b <{ true }> -> 
  ~ (st =[ while b do c end ]=> st').
Proof.
  intros b c st st' Hb.
  intros H.
  remember <{ while b do c end }> as cw eqn:Heqcw.
  induction H; inversion Heqcw; subst; clear Heqcw.
  - unfold bequiv in Hb. rewrite Hb in H. discriminate.
  - apply IHceval2. reflexivity.
Qed.

Theorem while_true : forall b c,
  bequiv b <{true}> ->
  cequiv
    <{ while b do c end }>
    <{ while true do skip end }>.
Proof.
  intros b c Hb. split; intros H; 
  exfalso; generalize dependent H; apply while_true_nonterm.
  - assumption.
  - unfold bequiv. reflexivity.
Qed.

Theorem loop_unrolling : forall b c,
  cequiv
    <{ while b do c end }>
    <{ if b then c ; while b do c end else skip end }>.
Proof.
  intros b c st st'.
  split; intros Hce.
  - inversion Hce; subst.
    * apply E_IfFalse.
      -- assumption.
      -- apply E_Skip.
    * apply E_IfTrue.
      -- assumption.
      -- apply E_Seq with (st' := st'0); assumption.
  - inversion Hce; subst.
    + inversion H5; subst.
      apply E_WhileTrue with (st' := st'0); assumption.
    + inversion H5; subst. apply E_WhileFalse. assumption.
Qed.

Theorem seq_assoc : forall c1 c2 c3,
  cequiv <{(c1;c2);c3}> <{c1;(c2;c3)}>.
Proof.
  intros c1 c2 c3 st st'.
  split; intros Hce.
  - inversion Hce; subst. inversion H1; subst.
    apply E_Seq with (st' := st'1).
    + assumption.
    + apply E_Seq with (st' := st'0).
      * assumption.
      * assumption.
  - inversion Hce; subst.
    inversion H4; subst.
    apply E_Seq with (st' := st'1).
    + apply E_Seq with (st' := st'0).
      * assumption.
      * assumption.
    + assumption.
Qed.

Theorem identity_assignment : forall x,
  cequiv
    <{ x := x }>
    <{ skip }>.
Proof.
  intros.
  split; intro H; inversion H; subst; clear H.
  - (* -> *)
    rewrite t_update_same.
    apply E_Skip.
  - (* <- *)
    assert (Hx : st' =[ x := x ]=> (x !-> st' x ; st')).
    { apply E_Asgn. reflexivity. }
    rewrite t_update_same in Hx.
    apply Hx.
Qed.
    
Theorem assign_aequiv : forall (X : string) (a : aexp),
  aequiv <{ X }> a ->
  cequiv <{ skip }> <{ X := a }>.
Proof.
  unfold aequiv. intros X a Ha st st'. split; intro H; inversion H; subst; clear H.
  Admitted.

Definition prog_a : com :=
  <{ while ~(X <= 0) do
       X := X + 1
     end }>.

Definition prog_b : com :=
  <{ if (X = 0) then
       X := X + 1;
       Y := 1
     else
       Y := 0
     end;
     X := X - Y;
     Y := 0 }>.

Definition prog_c : com :=
  <{ skip }> .
Definition prog_d : com :=
  <{ while X <> 0 do
       X := (X * Y) + 1
     end }>.
Definition prog_e : com :=
  <{ Y := 0 }>.
Definition prog_f : com :=
  <{ Y := X + 1;
     while X <> Y do
       Y := X + 1
     end }>.
Definition prog_g : com :=
  <{ while true do
       skip
     end }>.
  Definition prog_h : com :=
    <{ while X <> X do
         X := X + 1
       end }>.
  Definition prog_i : com :=
    <{ while X <> Y do
         X := Y + 1
       end }>.
Definition equiv_classes : list (list com) :=
[].

Lemma refl_aequv : forall (a : aexp),
  aequiv a a.
Proof.
  intros a st. reflexivity.
Qed.

Lemma sym_aequiv : forall (a1 a2 : aexp),
  aequiv a1 a2 -> aequiv a2 a1.
Proof.
  intros a1 a2 H. intros st. symmetry. apply H. Qed.

Lemma trans_aequiv : forall (a1 a2 a3 : aexp),
  aequiv a1 a2 -> aequiv a2 a3 -> aequiv a1 a3.
Proof.
  unfold aequiv. intros a1 a2 a3 H12 H23 st.
  rewrite H12. rewrite H23. reflexivity.
Qed.

Lemma refl_bequiv : forall (b : bexp),
  bequiv b b.
Proof.
  unfold bequiv. intros b st. reflexivity.
Qed.

Lemma sym_bequiv : forall (b1 b2 : bexp),
  bequiv b1 b2 -> bequiv b2 b1.
Proof.
  unfold bequiv. intros b1 b2 H. intros st. symmetry. apply H. Qed.

Lemma trans_bequiv : forall (b1 b2 b3 : bexp),
  bequiv b1 b2 -> bequiv b2 b3 -> bequiv b1 b3.
Proof.
  unfold bequiv. intros b1 b2 b3 H12 H23 st.
  rewrite H12. rewrite H23. reflexivity.
Qed.

Lemma refl_cequiv : forall (c : com),
  cequiv c c.
Proof.
  unfold cequiv. intros c st st'. reflexivity.
Qed.

Lemma sym_cequiv : forall (c1 c2 : com),
  cequiv c1 c2 -> cequiv c2 c1.
Proof.
  unfold cequiv. intros c1 c2 H st st'.
  rewrite H. reflexivity.
Qed.

Lemma trans_cequiv : forall (c1 c2 c3 : com),
  cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
Proof.
  unfold cequiv. intros c1 c2 c3 H12 H23 st st'.
  rewrite H12. apply H23.
Qed.

Theorem CAsgn_congruence : forall x a a',
  aequiv a a' ->
  cequiv <{x := a}> <{x := a'}>.
Proof.
  intros x a a' Heqv st st'.
  split; intros Hceval.
  - inversion Hceval. subst. apply E_Asgn. rewrite Heqv. reflexivity.
  - inversion Hceval. subst. apply E_Asgn. rewrite Heqv. reflexivity.
Qed.

Theorem CWhile_congruence : forall b b' c c',
  bequiv b b' -> cequiv c c' ->
  cequiv <{ while b do c end }> <{ while b' do c' end }>.
Proof.
  assert (A: forall (b b' : bexp) (c c' : com) (st st' : state),
      bequiv b b' -> cequiv c c' ->
      st =[ while b do c end ]=> st' ->
      st =[ while b' do c' end ]=> st').
  {
    unfold bequiv, cequiv.
    intros b b' c c' st st' Hbe Hc1e Hce.
    remember <{ while b do c end }> as cwhile eqn:Heqcwhile.
    induction Hce; inversion Heqcwhile; subst.
    + apply E_WhileFalse. rewrite <- Hbe. apply H.
    + apply E_WhileTrue with (st' := st').
      * rewrite <- Hbe. apply H.
      * apply Hc1e. apply Hce1.
      * apply IHHce2. reflexivity.
  }
  intros. split.
  - apply A; assumption.
  - apply A.
    + apply sym_bequiv. assumption.
    + apply sym_cequiv. assumption.
Qed.

Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv <{ c1;c2 }> <{ c1';c2' }>.
Proof.
  intros c1 c1' c2 c2' Hce1 Hce2 st st'.
  split; intros H; inversion H; subst.
  - apply E_Seq with st'0.
    + apply Hce1. apply H2.
    + apply Hce2. apply H5.
  - apply E_Seq with st'0.
    + apply Hce1. apply H2.
    + apply Hce2. apply H5.
Qed.    





    




  



