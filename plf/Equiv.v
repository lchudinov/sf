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

Definition cequive (c1 c2 : com) : Prop := 
  forall (st st' : state),
  (st =[ c1 ]=> st') <-> (st =[ c2 ]=> st').

Definition refines (c1 c2 : com) : Prop := 
  forall (st st' : state),
  (st =[ c1 ]=> st') -> (st =[ c2 ]=> st').
  
Theorem skip_left : forall c,
  cequive
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
  cequive
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
  cequive <{ if b then c1 else c2 end }>
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
  cequive <{ if b then c1 else c2 end }>
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
  cequive
    <{ if b then c1 else c2 end }>
    <{ if ~ b then c2 else c1 end }>.
Proof.
  unfold cequive. intros.
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
  cequive
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
  cequive
    <{ while b do c end }>
    <{ while true do skip end }>.
Proof.
  intros b c Hb. split; intros H; 
  exfalso; generalize dependent H; apply while_true_nonterm.
  - assumption.
  - unfold bequiv. reflexivity.
Qed.






    




  



