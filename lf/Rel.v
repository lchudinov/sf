Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export IndProp.

Definition relation (X: Type) := X -> X -> Prop.

Print le.
(* ====> Inductive le (n : nat) : nat -> Prop :=
             le_n : n <= n
           | le_S : forall m : nat, n <= m -> n <= S m *)
Check le : nat -> nat -> Prop.
Check le : relation nat.

Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Inductive next_nat : nat -> nat -> Prop :=
  | nn n : next_nat n (S n).
Check next_nat : relation nat.
Theorem next_nat_partial_function :
  partial_function next_nat.
Proof.
  unfold partial_function.
  intros x y1 y2 H1 H2.
  inversion H1. inversion H2.
  reflexivity. Qed.
  
  Theorem le_not_a_partial_function :
  not (partial_function le).
Proof.
  unfold not. unfold partial_function. intros Hc.
  assert (0 = 1) as Nonsense. {
    apply Hc with (x := 0).
    - apply le_n.
    - apply le_S. apply le_n. }
  discriminate Nonsense. Qed.
  
Check total_relation.

Inductive total_relation' : nat -> nat -> Prop :=
  | total_rel' (n m : nat) : total_relation' n m
.

Theorem total_relation_not_partial_function :
  not (partial_function total_relation').
Proof.
  unfold not. unfold partial_function.
  intros H.
  assert (0 = 1) as Nonsense. {
    apply (H 0 0 1). apply total_rel'. apply total_rel'.
  }
  discriminate Nonsense.
Qed.

Theorem empty_relation_partial_function :
  partial_function empty_relation.
Proof.
  unfold partial_function. intros. inversion H.
Qed.

Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.
Theorem le_reflexive :
  reflexive le.
Proof.
  unfold reflexive. intros n. apply le_n. Qed.
  
Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).
Theorem le_trans :
  transitive le.
  Proof.
    intros n m o Hnm Hmo.
    induction Hmo.
    - (* le_n *) apply Hnm.
    - (* le_S *) apply le_S. apply IHHmo. Qed.
  
Theorem lt_trans:
  transitive lt.
  Proof.
    unfold lt. unfold transitive.
    intros n m o Hnm Hmo.
    apply le_S in Hnm.
    apply le_trans with (a := (S n)) (b := (S m)) (c := o).
    apply Hnm.
    apply Hmo. Qed.

Theorem lt_trans' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [| m' Hm'o].
  - apply le_S in Hnm. apply Hnm.
  - apply le_S in IHHm'o. apply IHHm'o.
Qed.

Theorem lt_trans'' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction o as [| o'].
  - inversion Hmo.
  - apply le_trans with (S m).
    + apply le_S. apply Hnm.
    + apply Hmo.
Qed.

Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
Proof.
  intros n m H. apply le_trans with (S n).
  - apply le_S. apply le_n.
  - apply H.
Qed.

Theorem le_Sn_n : forall n,
  ~ (S n <= n).
Proof.
  intros n contra.
  induction n. inversion contra. apply le_S_n in contra. apply (IHn contra).
Qed.

Definition symmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a).

Theorem le_not_symmetric :
  not (symmetric le).
Proof.
  unfold symmetric. unfold not.
  intros H.
  assert (Nonsense: 1 <= 0). {
    apply (H 0 1). apply le_Sn_le. apply le_n.
  }
  inversion Nonsense.
Qed.

Definition antisymmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

Theorem le_antisymmetric :
  antisymmetric le.
  Proof.
    unfold antisymmetric. intros a b H1 H2.
    inversion H1.
    - reflexivity.
    - exfalso.
      rewrite <- H0 in H2.
      assert (Nonsense: S m <= m). {
        apply le_trans with a.
        apply H2.
        apply H.
      }
      apply (le_Sn_n m Nonsense).
Qed.

Definition equivalence {X:Type} (R: relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).

Definition order {X:Type} (R: relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).

Definition preorder {X:Type} (R: relation X) :=
  (reflexive R) /\ (transitive R).
Theorem le_order :
  order le.
Proof.
  unfold order. split.
    - (* refl *) apply le_reflexive.
    - split.
      + (* antisym *) apply le_antisymmetric.
      + (* transitive. *) apply le_trans. Qed.
