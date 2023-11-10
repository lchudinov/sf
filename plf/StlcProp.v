Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From PLF Require Import Types.
From PLF Require Import Stlc.
From PLF Require Import Smallstep.
Set Default Goal Selector "!".
Module STLCProp.
Import STLC.

Lemma canonical_forms_bool : forall t,
  empty |-- t \in Bool ->
  value t ->
  (t = <{true}>) \/ (t = <{false}>).
Proof.
  intros t HT HVal.
  destruct HVal; auto.
  inversion HT.
Qed.

Lemma canonical_forms_fun : forall t T1 T2,
  empty |-- t \in (T1 -> T2) ->
  value t ->
  exists x u, t = <{\x:T1, u}>.
Proof.
  intros t T1 T2 HT HVal.
  destruct HVal as [x ? t1 | |]; inversion HT; subst.
  exists x, t1. reflexivity.
Qed.

Theorem progress : forall t T,
  empty |-- t \in T ->
  value t \/ exists t', t --> t'.
Proof with eauto.
  intros t T Ht.
  remember empty as Gamma.
  induction Ht; subst Gamma; auto.
    (* auto solves all three cases in which t is a value *)
  - (* T_Var *)
    (* contradictory: variables cannot be typed in an empty context *)
    discriminate H.
  - (* T_App *)
    (* t = t1 t2. Proced by cases on whether t1 is a value or steps... *)
    right. destruct IHHt1...
    + (* t1 is a value *)
      destruct IHHt2...
      * (* t2 is also a value *)
        eapply canonical_forms_fun in Ht1; [|assumption].
        destruct Ht1 as [x [t0 H1]]. subst.
        exists (<{ [x:=t2]t0 }>)...
      * (* t2 steps *)
        destruct H0 as [t2' Hstp]. exists (<{ t1 t2' }>)...
    + (* t1 steps *)
      destruct H as [t1' Hstp]. exists (<{ t1' t2 }>)...
  - (* TIf *)
    right. destruct IHHt1...
    + (* t1 is a value *)
      destruct (canonical_forms_bool t1); subst; eauto.
    + (* t1 also steps *)
      destruct H as [t1' Hstp]. exists (<{ if t1' then t2 else t3 }>)...
Qed.


Theorem progress' : forall t T,
     empty |-- t \in T ->
     value t \/ exists t', t --> t'.
Proof.
  intros t.
  induction t; intros T Ht; auto.
Admitted.
  
        
  
  
End STLCProp.

