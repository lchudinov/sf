Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Arith.Arith.
From PLF Require Import Maps.
From PLF Require Import Smallstep.
Set Default Goal Selector "!".
Hint Constructors multi : core.

Module TM.
Inductive tm : Type :=
  | tru : tm
  | fls : tm
  | ite : tm -> tm -> tm -> tm
  | zro : tm
  | scc : tm -> tm
  | prd : tm -> tm
  | iszro : tm -> tm.

Declare Custom Entry tm.
Declare Scope tm_scope.
Notation "'true'" := true (at level 1): tm_scope.
Notation "'true'" := (tru) (in custom tm at level 0): tm_scope.
Notation "'false'" := false (at level 1): tm_scope.
Notation "'false'" := (fls) (in custom tm at level 0): tm_scope.
Notation "<{ e }>" := e (e custom tm at level 99): tm_scope.
Notation "( x )" := x (in custom tm, x at level 99): tm_scope.
Notation "x" := x (in custom tm at level 0, x constr at level 0): tm_scope.
Notation "'0'" := (zro) (in custom tm at level 0): tm_scope.
Notation "'0'" := 0 (at level 1): tm_scope.
Notation "'succ' x" := (scc x) (in custom tm at level 90, x custom tm at level 80): tm_scope.
Notation "'pred' x" := (prd x) (in custom tm at level 90, x custom tm at level 80): tm_scope.
Notation "'iszero' x" := (iszro x) (in custom tm at level 80, x custom tm at level 70): tm_scope.
Notation "'if' c 'then' t 'else' e" := (ite c t e)
                 (in custom tm at level 90, c custom tm at level 80,
                  t custom tm at level 80, e custom tm at level 80): tm_scope.
Local Open Scope tm_scope.

Inductive bvalue : tm -> Prop :=
  | bv_True : bvalue <{ true }>
  | bv_false : bvalue <{ false }>.
Inductive nvalue : tm -> Prop :=
  | nv_0 : nvalue <{ 0 }>
  | nv_succ : forall t, nvalue t -> nvalue <{ succ t }>.
Definition value (t : tm) := bvalue t \/ nvalue t.
Hint Constructors bvalue nvalue : core.
Hint Unfold value : core.

Reserved Notation "t '-->' t'" (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      <{ if true then t1 else t2 }> --> t1
  | ST_IfFalse : forall t1 t2,
      <{ if false then t1 else t2 }> --> t2
  | ST_If : forall c c' t2 t3,
      c --> c' ->
      <{ if c then t2 else t3 }> --> <{ if c' then t2 else t3 }>
  | ST_Succ : forall t1 t1',
      t1 --> t1' ->
      <{ succ t1 }> --> <{ succ t1' }>
  | ST_Pred0 :
      <{ pred 0 }> --> <{ 0 }>
  | ST_PredSucc : forall v,
      nvalue v ->
      <{ pred (succ v) }> --> v
  | ST_Pred : forall t1 t1',
      t1 --> t1' ->
      <{ pred t1 }> --> <{ pred t1' }>
  | ST_Iszero0 :
      <{ iszero 0 }> --> <{ true }>
  | ST_IszeroSucc : forall v,
       nvalue v ->
      <{ iszero (succ v) }> --> <{ false }>
  | ST_Iszero : forall t1 t1',
      t1 --> t1' ->
      <{ iszero t1 }> --> <{ iszero t1' }>

where "t '-->' t'" := (step t t').
Hint Constructors step : core.

Notation step_normal_form := (normal_form step).
Definition stuck (t : tm) : Prop :=
  step_normal_form t /\ ~ value t.
Hint Unfold stuck : core.

Example some_term_is_stuck :
  exists t, stuck t.
Proof.
  exists <{ iszero false }>.
  unfold stuck. split.
  - unfold step_normal_form. unfold not.
    intros. destruct H as [t1 H]. inversion H. inversion H1.
  - unfold not. intros. inversion H.
    * inversion H0.
    * inversion H0.
Qed.

Lemma value_is_nf : forall t,
  value t -> step_normal_form t.
Proof.
  intros t H. inversion H.
  - destruct H0.
    + unfold step_normal_form.
      unfold not. intros. destruct H0 as [t1 H0].
      inversion H0.
      + unfold step_normal_form.
      unfold not. intros. destruct H0 as [t1 H0].
      inversion H0.
      - induction H0.
      + unfold step_normal_form.
        unfold not. intros. destruct H0 as [t1 H0].
        inversion H0.
      + unfold step_normal_form.
        unfold not. intros.
        inversion H0. 
        * destruct H1 as [t' H1].
          rewrite <- H2 in H1. inversion H1. inversion H4.
        * destruct H1 as [t' H1]. clear H1.
          inversion H2; clear H2.
          ** rewrite <- H1 in H3.
          rewrite <- H3 in IHnvalue.
Admitted.