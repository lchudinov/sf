Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Init.Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From PLF Require Import Maps.
From PLF Require Import Imp.
Set Default Goal Selector "!".
Definition FILL_IN_HERE := <{True}>.

Inductive tm : Type :=
  | C : nat -> tm (* Constant *)
  | P : tm -> tm -> tm. (* Plus *)
  
Fixpoint evalF (t : tm) : nat :=
  match t with
  | C n => n
  | P t1 t2 => evalF t1 + evalF t2
  end.
  
Reserved Notation " t '==>' n " (at level 50, left associativity).

Inductive eval : tm -> nat -> Prop :=
  | E_Const : forall n, C n ==> n
  | E_Plus : forall t1 t2 v1 v2,
    t1 ==> v1 ->
    t2 ==> v2 ->
    P t1 t2 ==> (v1 + v2)
where " t '==>' n " := (eval t n).

Module SimpleArith1.
    