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

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall v1 v2,
    P (C v1) (C v2) --> C (v1 + v2)
  | ST_Plus1 : forall t1 t1' t2,
    t1 --> t1' ->
    P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
    t2 --> t2' ->
    P (C v1) t2 --> P (C v1) t2'
  
  where " t '-->' t' " := (step t t').

Example test_step_1 :
      P
        (P (C 1) (C 3))
        (P (C 2) (C 4))
      -->
      P
        (C 4)
        (P (C 2) (C 4)).
Proof.
  apply ST_Plus1. apply ST_PlusConstConst.
Qed.

Example test_step_2 :
      P
        (C 0)
        (P
          (C 2)
          (P (C 1) (C 3)))
      -->
      P
        (C 0)
        (P
          (C 2)
          (C 4)).
Proof.
  apply ST_Plus2.
  apply ST_Plus2.
  apply ST_PlusConstConst.
Qed.

End SimpleArith1.


Definition relation (X : Type) := X -> X -> Prop.

Definition deterministic {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.
Module SimpleArith2.
Import SimpleArith1.

Theorem step_deterministic:
  deterministic step.
Proof.
  unfold deterministic. intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2.
  - inversion Hy2; subst.
    + reflexivity.
    + inversion H2.
    + inversion H2.
  - inversion Hy2; subst.
    + inversion Hy1.
    + apply IHHy1 in H2. rewrite H2. reflexivity.
    + inversion Hy1.
  - inversion Hy2; subst.
    + inversion Hy1.
    + inversion H2.
    + apply IHHy1 in H2. rewrite H2. reflexivity.
Qed.

End SimpleArith2.

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

Ltac solve_by_invert :=
  solve_by_inverts 1.

Module SimpleArith3.
Import SimpleArith1.
Theorem step_deterministic_alt: deterministic step.
Proof.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2;
    inversion Hy2; subst; try solve_by_invert.
  - reflexivity.
  - apply IHHy1 in H2. rewrite H2. reflexivity.
  - apply IHHy1 in H2. rewrite H2. reflexivity.
Qed.

End SimpleArith3.

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n).

Reserved Notation " t '-->' t' " (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall v1 v2,
          P (C v1) (C v2)
      --> C (v1 + v2)
  | ST_Plus1 : forall t1 t1' t2,
        t1 --> t1' ->
        P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
        value v1 -> (* <--- n.b. *)
        t2 --> t2' ->
        P v1 t2 --> P v1 t2'

  where " t '-->' t' " := (step t t').
  
Theorem step_deterministic :
  deterministic step.
Proof.
  unfold deterministic. intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2.
  - inversion Hy2; subst.
    + reflexivity.
    + inversion H2.
    + inversion H3.
  - inversion Hy2; subst.
    + inversion Hy1.
    + apply IHHy1 in H2. rewrite H2. reflexivity.
    + inversion H1; subst. inversion Hy1.
  - inversion Hy2; subst.
    + inversion Hy1.
    + inversion H; subst. inversion H3.
    + apply IHHy1 in H4. rewrite H4. reflexivity.
Qed.

Theorem strong_progress : forall t,
  value t \/ (exists t', t --> t').
Proof.
  induction t.
  - (* C *) left. apply v_const.
  - (* P *) right. destruct IHt1 as [IHt1 | [t1' Ht1] ].
    + (* l *) destruct IHt2 as [IHt2 | [t2' Ht2] ].
      * (* l *) inversion IHt1. inversion IHt2.
        exists (C (n + n0)).
        apply ST_PlusConstConst.
      * (* r *)
        exists (P t1 t2').
        apply ST_Plus2; auto.
    + (* r *)
      exists (P t1' t2).
      apply ST_Plus1. apply Ht1.
Qed.

Definition normal_form {X : Type}
              (R : relation X) (t : X) : Prop :=
  ~ exists t', R t t'.
  
Lemma value_is_nf : forall v,
  value v -> normal_form step v.
Proof.
  unfold normal_form. intros v H. destruct H.
  intros contra. destruct contra. inversion H.
Qed.

Lemma nf_is_value : forall t,
  normal_form step t -> value t.
Proof. (* a corollary of strong_progress... *)
  unfold normal_form. intros t H.
  assert (G : value t \/ exists t', t --> t').
  { apply strong_progress. }
  destruct G as [G | G].
  - (* l *) apply G.
  - (* r *) contradiction.
Qed.

Corollary nf_same_as_value : forall t,
  normal_form step t <-> value t.
Proof.
  split.
  - apply nf_is_value.
  - apply value_is_nf.
Qed.

Module Temp1.
Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n)
  | v_funny : forall t1 v2,
                value (P t1 (C v2)). (* <--- *)
Reserved Notation " t '-->' t' " (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall v1 v2,
      P (C v1) (C v2) --> C (v1 + v2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      P v1 t2 --> P v1 t2'

  where " t '-->' t' " := (step t t').

Lemma value_not_same_as_normal_form :
  exists v, value v /\ ~ normal_form step v.
Proof.
  exists (P (P (C 1) (C 3)) (C 1)).
  split.
  - apply v_funny.
  - unfold normal_form.
    intros H.
    unfold not in H.
    apply H. clear H.
    exists (P (C 4) (C 1)).
    apply ST_Plus1.
    apply ST_PlusConstConst.
Qed.
End Temp1.

Module Temp2.
Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n). (* Original definition *)
Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_Funny : forall n,
      C n --> P (C n) (C 0) (* <--- NEW *)
  | ST_PlusConstConst : forall v1 v2,
      P (C v1) (C v2) --> C (v1 + v2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      P v1 t2 --> P v1 t2'

  where " t '-->' t' " := (step t t').

Lemma value_not_same_as_normal_form :
  exists v, value v /\ ~ normal_form step v.
Proof.
  exists (C 1).
  split.
  - apply v_const.
  - unfold normal_form.
    intros H. unfold not in H. apply H. clear H.
    exists (P (C 1) (C 0)).
    apply ST_Funny.
Qed.

End Temp2.

Module Temp3.
Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n).
Reserved Notation " t '-->' t' " (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall v1 v2,
      P (C v1) (C v2) --> C (v1 + v2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2

  where " t '-->' t' " := (step t t').

Lemma value_not_same_as_normal_form :
  exists t, ~ value t /\ normal_form step t.
Proof.
  exists (P (C 1) (P (C 1) (C 1))).
  split.
  - intro H. inversion H.
  - unfold normal_form.
    intros H.
    destruct H as [x H].
    inversion H.
    inversion H3.
Qed.
End Temp3.

Module Temp4.
Inductive tm : Type :=
  | tru : tm
  | fls : tm
  | test : tm -> tm -> tm -> tm.
Inductive value : tm -> Prop :=
  | v_tru : value tru
  | v_fls : value fls.
Reserved Notation " t '-->' t' " (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      test tru t1 t2 --> t1
  | ST_IfFalse : forall t1 t2,
      test fls t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      test t1 t2 t3 --> test t1' t2 t3

  where " t '-->' t' " := (step t t').
  
Definition bool_step_prop1 :=
  fls --> fls.
Example bool_step_prop1_ex: ~ bool_step_prop1.
Proof.
  unfold bool_step_prop1.
  intros H. inversion H.
Qed.
  
Definition bool_step_prop2 :=
     test
       tru
       (test tru tru tru)
       (test fls fls fls)
  -->
     tru.
Example bool_step_prop2_ex: ~ bool_step_prop2.
Proof.
  unfold bool_step_prop2.
  intros H.
  inversion H.
Qed.

Definition bool_step_prop3 :=
     test
       (test tru tru tru)
       (test tru tru tru)
       fls
   -->
     test
       tru
       (test tru tru tru)
       fls.
Example bool_step_prop3_ex: bool_step_prop3.
Proof.
  unfold bool_step_prop3.
  apply ST_If.
  apply ST_IfTrue.
Qed.

Theorem strong_progress_bool : forall t,
  value t \/ (exists t', t --> t').
Proof.
  induction t.
  - left. apply v_tru.
  - left. apply v_fls.
  - right. 
    destruct IHt1 as [IHt1 | [t1' IHt1]];
    destruct IHt2 as [IHt2 | [t2' IHt2]];
    destruct IHt3 as [IHt3 | [t3' IHt3]].
    + inversion IHt1; inversion IHt2; inversion IHt3.
      * exists tru. apply ST_IfTrue.
      * exists tru. apply ST_IfTrue.
      * exists fls. apply ST_IfTrue.
      * exists fls. apply ST_IfTrue.
      * exists tru. apply ST_IfFalse.
      * exists fls. apply ST_IfFalse.
      * exists tru. apply ST_IfFalse.
      * exists fls. apply ST_IfFalse.
    + inversion IHt1; inversion IHt2.
      * exists tru. apply ST_IfTrue.
      * exists fls. apply ST_IfTrue.
      * exists t3. apply ST_IfFalse.
      * exists t3. apply ST_IfFalse.
    + inversion IHt1; inversion IHt3.
      * exists t2. apply ST_IfTrue.
      * exists t2. apply ST_IfTrue.
      * exists tru. apply ST_IfFalse.
      * exists fls. apply ST_IfFalse.
    + inversion IHt1; inversion IHt2; subst.
      * exists (test tru t2' t4). apply ST_IfTrue.
      * exists (test fls t0 t2'). apply ST_IfTrue.
      * exists (test t0 t4 t5). apply ST_IfTrue.
      * exists t3. apply ST_IfFalse.
      * exists t3. apply ST_IfFalse.
      * exists t3. apply ST_IfFalse.
    + inversion IHt2; inversion IHt3; subst.
      * exists (test t1' tru tru). apply ST_If. assumption.
      * exists (test t1' tru fls). apply ST_If. assumption.
      * exists (test t1' fls tru). apply ST_If. assumption.
      * exists (test t1' fls fls). apply ST_If. assumption.
    + inversion IHt2; subst.
      * exists (test t1' tru t3). apply ST_If. assumption.
      * exists (test t1' fls t3). apply ST_If. assumption.
    + inversion IHt3.
      * exists (test t1' t2 tru). apply ST_If. assumption.
      * exists (test t1' t2 fls). apply ST_If. assumption.
    + exists (test t1' t2 t3). apply ST_If. assumption.
Qed.

Theorem step_deterministic : deterministic step.
Proof.
  unfold deterministic.
  unfold deterministic. intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2.
  - inversion Hy2; subst.
    + reflexivity.
    + inversion H3.
  - inversion Hy2; subst.
    + reflexivity.
    + inversion H3.
  - inversion Hy2; subst.
    + inversion Hy1.
    + inversion Hy1.
    + apply IHHy1 in H3. rewrite H3. reflexivity.
Qed.
Module Temp5.

Reserved Notation " t '-->' t' " (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      test tru t1 t2 --> t1
  | ST_IfFalse : forall t1 t2,
      test fls t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      test t1 t2 t3 --> test t1' t2 t3
  | ST_ShortCircuit : forall t1 t2,
      value t2 ->
      test t1 t2 t2 --> t2
  where " t '-->' t' " := (step t t').
Definition bool_step_prop4 :=
         test
            (test tru tru tru)
            fls
            fls
     -->
         fls.
Example bool_step_prop4_holds :
  bool_step_prop4.
Proof.
  unfold bool_step_prop4.
  apply ST_ShortCircuit.
  apply v_fls.
Qed.

Goal ~ forall n1 n2 x, x + 1 = n1 -> x + 2 = n2 -> n1 = n2.
Proof.
  intro H.
  specialize (H 1 2 0 eq_refl eq_refl).
  discriminate.
Qed.

Theorem step_deterministic : ~ deterministic step.
Proof.
  unfold deterministic.
  intros H.
  specialize (H (test (test tru tru tru) tru tru) tru (test tru tru tru)).
  discriminate H.
  - apply ST_ShortCircuit. apply v_tru.
  - apply ST_If. apply ST_IfTrue.
Qed.

Theorem strong_progress_bool : forall t,
  value t \/ (exists t', t --> t').
Proof.
Admitted.

(*
In general, is there any way we could cause strong progress to fail if we took away one or more constructors from the original step relation? Write yes or no and briefly (1 sentence) explain your answer.
Yes, we for example took away ST_If it would cause strong progess to fail.
*)

End Temp5.
End Temp4.


Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.
                    
Notation " t '-->*' t' " := (multi step t t') (at level 40).

Theorem multi_R : forall (X : Type) (R : relation X) (x y : X),
    R x y -> (multi R) x y.
Proof.
  intros X R x y H.
  apply multi_step with y.
  - apply H.
  - apply multi_refl.
Qed.

Theorem multi_trans :
  forall (X : Type) (R : relation X) (x y z : X),
      multi R x y ->
      multi R y z ->
      multi R x z.
Proof.
  intros X R x y z G H.
  induction G.
    - (* multi_refl *) assumption.
    - (* multi_step *)
      apply multi_step with y.
      + assumption.
      + apply IHG. assumption.
Qed.


Lemma test_multistep_1:
      P
        (P (C 0) (C 3))
        (P (C 2) (C 4))
   -->*
      C ((0 + 3) + (2 + 4)).
Proof.
  apply multi_step with 
          (P (C (0 + 3))
          (P (C 2) (C 4))).
  { apply ST_Plus1. apply ST_PlusConstConst. }
  apply multi_step with 
          (P (C (0 + 3))
             (C (2 + 4))).
  { apply ST_Plus2.
    - apply v_const.
    - apply ST_PlusConstConst.
  }
  apply multi_R.
  apply ST_PlusConstConst.
Qed.

Lemma test_multistep_1':
      P
        (P (C 0) (C 3))
        (P (C 2) (C 4))
   -->*
      C ((0 + 3) + (2 + 4)).
Proof.
  eapply multi_step. { apply ST_Plus1. apply ST_PlusConstConst. }
  eapply multi_step. {
                        apply ST_Plus2.
                        - apply v_const.
                        - apply ST_PlusConstConst.
                     }
  apply multi_R.
  apply ST_PlusConstConst.
Qed.

Lemma test_multistep_2:
  C 3 -->* C 3.
Proof.
  apply multi_refl.
Qed.

Lemma test_multistep_3:
      P (C 0) (C 3)
   -->*
      P (C 0) (C 3).
Proof.
  apply multi_refl.
Qed.

Lemma test_multistep_4:
      P
        (C 0)
        (P
          (C 2)
          (P (C 0) (C 3)))
  -->*
      P
        (C 0)
        (C (2 + (0 + 3))).
Proof.
  eapply multi_step. { apply ST_Plus2.
                       - apply v_const.
                       - apply ST_Plus2.
                         * apply v_const.
                         * apply ST_PlusConstConst.
                     }
  eapply multi_step. { - apply ST_Plus2.
                         + apply v_const.
                         + apply ST_PlusConstConst.
                     }
  apply multi_refl.
Qed.

Definition step_normal_form := normal_form step.
Definition normal_form_of (t t' : tm) :=
  (t -->* t' /\ step_normal_form t').
  
Theorem normal_forms_unique:
  deterministic normal_form_of.
Proof.
  (* We recommend using this initial setup as-is! *)
  unfold deterministic. unfold normal_form_of.
  intros x y1 y2 P1 P2.
  destruct P1 as [P11 P12].
  destruct P2 as [P21 P22].
  unfold step_normal_form in *.
  apply nf_same_as_value in P12.
  apply nf_same_as_value in P22.
  destruct P12 as [v1].
  destruct P22 as [v2].
  Admitted.

Definition normalizing {X : Type} (R : relation X) :=
  forall t, exists t',
    (multi R) t t' /\ normal_form R t'.
    
Lemma multistep_congr_1 : forall t1 t1' t2,
    t1 -->* t1' ->
    P t1 t2 -->* P t1' t2.
Proof.
 intros t1 t1' t2 H. induction H.
 - (* multi_refl *) apply multi_refl.
 - (* multi_step *) apply multi_step with (P y t2).
   + apply ST_Plus1. apply H.
   + apply IHmulti.
Qed.

Lemma multistep_congr_2 : forall v1 t2 t2',
     value v1 ->
     t2 -->* t2' ->
     P v1 t2 -->* P v1 t2'.
Proof.
  intros v1 t2 t2' H1 H2. induction H2.
  - (* multi_refl *) apply multi_refl.
  - (* multi_step *) apply multi_step with (P v1 y).
    + apply ST_Plus2.
      * apply H1.
      * apply H.
    + apply IHmulti.
Qed.

Theorem step_normalizing :
  normalizing step.
Proof.
  unfold normalizing.
  induction t.
  - (* C *)
    exists (C n).
    split.
    + (* l *) apply multi_refl.
    + (* r *)
      (* We can use rewrite with "iff" statements, not
           just equalities: *)
      apply nf_same_as_value. apply v_const.
  - (* P *)
    destruct IHt1 as [t1' [Hsteps1 Hnormal1] ].
    destruct IHt2 as [t2' [Hsteps2 Hnormal2] ].
    apply nf_same_as_value in Hnormal1.
    apply nf_same_as_value in Hnormal2.
    destruct Hnormal1 as [v1].
    destruct Hnormal2 as [v2].
    exists (C (v1 + v2)).
    split.
    + (* l *)
      apply multi_trans with (P (C v1) t2).
      * apply multistep_congr_1. apply Hsteps1.
      * apply multi_trans with (P (C v1) (C v2)).
        { apply multistep_congr_2.
          - apply v_const.
          - apply Hsteps2. }
        apply multi_R. apply ST_PlusConstConst.
    + (* r *)
      apply nf_same_as_value. apply v_const.
Qed.


