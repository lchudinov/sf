From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.
Set Default Goal Selector "!".

Locate "+".
Print Init.Nat.add.

Check String.eqb_refl :
  forall x : string, (x =? x)%string = true.
Check String.eqb_eq :
  forall n m : string, (n =? m)%string = true <-> n = m.
Check String.eqb_neq :
  forall n m : string, (n =? m)%string = false <-> n <> m.
Check String.eqb_spec :
  forall x y : string, reflect (x = y) (String.eqb x y).
  
Definition total_map (A : Type) := string -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A : Type} (m : total_map A) (x : string) (v : A) :=
  fun x' => if String.eqb x x' then v else m x'.

Definition examplemap := t_update (t_update (t_empty false) "foo" true) "bar" true.

Notation "'_' '!->' v" :=
  (t_empty v)
  (at level 100, right associativity).

Example example_empty := (_ !-> false).

Notation "x '!->' v ';' m" :=
  (t_update m x v)
  (at level 100, v at next level, right associativity).

Definition examplemap' := 
  ( "bar" !-> true;
    "foo" !-> true;
    _ !-> false
  ).
  
Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
  (_ !-> v) x = v.
Proof. intros. reflexivity. Qed.

Lemma t_update_eq : forall (A : Type) (m : total_map A) (x : string) (v : A),
  (x !-> v ; m) x = v.
Proof.
  intros. unfold t_update. rewrite String.eqb_refl. reflexivity.
Qed.

Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
  x1 <> x2 -> (x1 !-> v ; m) x2 = m x2.
Proof.
  intros. unfold t_update. apply String.eqb_neq in H. rewrite H. reflexivity.
Qed.

Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
  (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  intros. apply functional_extensionality.
  intros. unfold t_update.
  destruct ((x =? x0)%string).
  - reflexivity.
  - reflexivity.
Qed.
  
Theorem t_update_same : forall (A : Type) (m : total_map A) x,
  (x !-> m x ; m) = m.
Proof.
  intros. apply functional_extensionality.
  intros. unfold t_update. destruct (String.eqb_spec x x0).
  - rewrite e. reflexivity.
  - reflexivity.
Qed.

Theorem t_update_permute : forall (A : Type) (m : total_map A) v1 v2 x1 x2,
  x2 <> x1 ->
  (x1 !-> v1 ; x2 !-> v2 ; m)
  =
  (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
  intros. apply functional_extensionality. intros.
  unfold t_update. destruct (String.eqb_spec x x1).
  - destruct (String.eqb_spec x2 x).
    + rewrite <- e. rewrite <- e0. rewrite String.eqb_refl.
      unfold not in H. apply String.eqb_neq in H.
      rewrite <- e in H. rewrite e0 in H.
      rewrite String.eqb_refl in H. discriminate H.
    +  rewrite <- e. rewrite String.eqb_refl. reflexivity.
  - destruct (String.eqb_spec x2 x).
    + unfold not in n. apply String.eqb_neq in n. rewrite String.eqb_sym in n.
      rewrite n. reflexivity.
    + reflexivity.
Qed.



  




