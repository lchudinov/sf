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


    




  



