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
  - inversion H0.
    + unfold step_normal_form.
      unfold not. intros. destruct H2 as [t1 H2].
      inversion H2.
      + unfold step_normal_form.
        unfold not. intros. destruct H2 as [t1 H2].
        inversion H2.
      - induction t; try inversion H0.
        + unfold step_normal_form, not. intros.
          destruct H1 as [t' H1].
          inversion H1.
        + unfold step_normal_form, not. intros.
          destruct H3 as [t' H3].
Admitted.

Theorem step_deterministic:
  deterministic step.
Proof with eauto.
  unfold deterministic. intros x y1 y2 H1 H2.
  induction x.
  - inversion H1; inversion H2; subst.
  - inversion H1; inversion H2; subst.
  - inversion H1; inversion H2; subst; clear H1; clear H2.
Admitted.

Inductive ty : Type :=
  | Bool : ty
  | Nat : ty.
  
  Reserved Notation "'|--' t '\in' T" (at level 40).

  Inductive has_type : tm -> ty -> Prop :=
    | T_True :
         |-- <{ true }> \in Bool
    | T_False :
         |-- <{ false }> \in Bool
    | T_If : forall t1 t2 t3 T,
         |-- t1 \in Bool ->
         |-- t2 \in T ->
         |-- t3 \in T ->
         |-- <{ if t1 then t2 else t3 }> \in T
    | T_0 :
         |-- <{ 0 }> \in Nat
    | T_Succ : forall t1,
         |-- t1 \in Nat ->
         |-- <{ succ t1 }> \in Nat
    | T_Pred : forall t1,
         |-- t1 \in Nat ->
         |-- <{ pred t1 }> \in Nat
    | T_Iszero : forall t1,
         |-- t1 \in Nat ->
         |-- <{ iszero t1 }> \in Bool
  
  where "'|--' t '\in' T" := (has_type t T).
  
  Hint Constructors has_type : core.
  
Example has_type_1 :
  |-- <{ if false then 0 else (succ 0) }> \in Nat.
Proof.
  apply T_If.
    - apply T_False.
    - apply T_0.
    - apply T_Succ. apply T_0.
Qed.

Example has_type_not :
  ~ ( |-- <{ if false then 0 else true}> \in Bool ).
Proof.
  intros Contra. solve_by_inverts 2.
Qed.

Example succ_hastype_nat__hastype_nat : forall t,
  |-- <{succ t}> \in Nat ->
  |-- t \in Nat.
Proof. 
  intros t H.
  inversion H.
  assumption.
Qed.

Lemma bool_canonical : forall t,
  |-- t \in Bool -> value t -> bvalue t.
Proof.
  intros t HT [Hb | Hn].
  - assumption.
  - destruct Hn as [ | Hs].
    + inversion HT.
    + inversion HT.
Qed.

Lemma nat_canonical : forall t,
  |-- t \in Nat -> value t -> nvalue t.
Proof.
  intros t HT [Hb | Hn].
  - inversion Hb; subst; inversion HT.
  - assumption.
Qed.

Theorem progress : forall t T,
  |-- t \in T ->
  value t \/ exists t', t --> t'.
Proof.
  intros t T HT.
  induction HT; auto.
  (* The cases that were obviously values, like T_True and
     T_False, are eliminated immediately by auto *)
  - (* T_If *)
    right. destruct IHHT1.
    + (* t1 is a value *)
    apply (bool_canonical t1 HT1) in H.
    destruct H.
      * exists t2. auto.
      * exists t3. auto.
    + (* t1 can take a step *)
      destruct H as [t1' H1].
      exists (<{ if t1' then t2 else t3 }>). auto.
  - inversion IHHT; clear IHHT.
    + inversion H; clear H.
      * solve_by_inverts 2.
      * left. right. constructor. assumption.
    + right. inversion H. exists (<{ succ x }>). constructor. assumption.
  - right. inversion IHHT; clear IHHT.
    + inversion H; clear H.
      * solve_by_inverts 2.
      * inversion H0; clear H0.
        ** exists <{ 0 }>. constructor.
        ** exists <{ t }>. constructor. assumption.
    + inversion H; clear H.
      * exists <{ pred x}>. constructor. assumption.
  - right. inversion IHHT; clear IHHT.
    + inversion H; clear H.
      * solve_by_inverts 2.
      * inversion H0; clear H0.
        ** exists <{ true }>. constructor.
        ** exists <{ false }>. constructor. assumption.
    + inversion H.
      exists <{ iszero x}>. constructor. assumption.
Qed.

Theorem preservation : forall t t' T,
  |-- t \in T ->
  t --> t' ->
  |-- t' \in T.
Proof.
  intros t t' T HT HE.
  generalize dependent t'.
  induction HT;
         (* every case needs to introduce a couple of things *)
         intros t' HE;
         (* and we can deal with several impossible
            cases all at once *)
         try solve_by_invert.
    - (* T_If *) inversion HE; subst; clear HE.
      + (* ST_IFTrue *) assumption.
      + (* ST_IfFalse *) assumption.
      + (* ST_If *) apply T_If; try assumption.
        apply IHHT1; assumption.
    - inversion HE; subst; clear HE.
      apply T_Succ. apply IHHT. assumption.
    - inversion HE; subst; clear HE.
      + assumption.
      + inversion HT; subst. assumption.
      + apply T_Pred. apply IHHT. assumption.
    - inversion HE; subst; clear HE.
      + constructor.
      + constructor.
      + constructor. apply IHHT. assumption.
Qed.

Theorem preservation' : forall t t' T,
  |-- t \in T ->
  t --> t' ->
  |-- t' \in T.
Proof with eauto.
  intros t t' T HT HE.
  generalize dependent T.
  induction HE; intros T HT.
  - inversion HT; subst; clear HT.
    assumption.
  - inversion HT; subst; clear HT.
    assumption.
  - inversion HT; subst; clear HT.
    apply T_If; try assumption.
    apply IHHE. assumption.
  - inversion HT; subst; clear HT.
    apply IHHE in H0. apply T_Succ in H0. assumption.
  - inversion HT; subst; clear HT. assumption.
  - inversion HT; subst.
    inversion H1; subst. assumption.
  - inversion HT; subst.
    apply T_Pred. apply IHHE. assumption.
  - inversion HT; subst. constructor.
  - inversion HT; subst. constructor.
  - inversion HT; subst. constructor. apply IHHE. assumption.
Qed.

Definition multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).
Corollary soundness : forall t t' T,
  |-- t \in T ->
  t -->* t' ->
  ~(stuck t').
Proof.
  intros t t' T HT P. induction P; intros [R S].
  - apply progress in HT. destruct HT; auto.
  - apply IHP.
    + apply preservation with (t := x); auto.
    + unfold stuck. split; auto.
Qed.

Theorem subject_expansion:
  (forall t t' T, t --> t' /\ |-- t' \in T -> |-- t \in T)
  \/
  ~ (forall t t' T, t --> t' /\ |-- t' \in T -> |-- t \in T).
Proof with eauto.
  right.
  intros contra.
  specialize contra with (t:= <{ if true then true else 0 }>).
  specialize contra with (t' := <{ true }>).
  specialize contra with (T := Bool).
  Admitted.
  

  


      
  