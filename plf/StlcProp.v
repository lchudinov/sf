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

Lemma weakening : forall Gamma Gamma' t T,
     includedin Gamma Gamma' ->
     Gamma |-- t \in T ->
     Gamma' |-- t \in T.
Proof.
  intros Gamma Gamma' t T H Ht.
  generalize dependent Gamma'.
  induction Ht; eauto using includedin_update.
Qed.

Lemma weakening_empty : forall Gamma t T,
     empty |-- t \in T ->
     Gamma |-- t \in T.
Proof.
  intros Gamma t T.
  eapply weakening.
  discriminate.
Qed.
  
Lemma substitution_preserves_typing : forall Gamma x U t v T,
  x |-> U ; Gamma |-- t \in T ->
  empty |-- v \in U ->
  Gamma |-- [x:=v]t \in T.
Proof.
  intros Gamma x U t v T Ht Hv.
  generalize dependent Gamma. generalize dependent T.
  induction t; intros T Gamma H;
  (* in each case, we'll want to get at the derivation of H *)
    inversion H; clear H; subst; simpl; eauto.
  - (* var *)
    rename s into y. destruct (eqb_spec x y); subst.
    + (* x=y *)
      rewrite update_eq in H2.
      injection H2 as H2; subst.
      apply weakening_empty. assumption.
    + (* x<>y *)
      apply T_Var. rewrite update_neq in H2; auto.
  - (* abs *)
    rename s into y, t into S.
    destruct (eqb_spec x y); subst; apply T_Abs.
    + (* x=y *)
      rewrite update_shadow in H5. assumption.
    + (* x<>y *)
      apply IHt.
      rewrite update_permute; auto.
Qed.

Lemma substitution_preserves_typing_from_typing_ind : forall Gamma x U t v T,
  x |-> U ; Gamma |-- t \in T ->
  empty |-- v \in U ->
  Gamma |-- [x:=v]t \in T.
Proof.
  intros Gamma x U t v T Ht Hv.
  remember (x |-> U; Gamma) as Gamma'.
  generalize dependent Gamma.
  induction Ht; intros Gamma' G; simpl; eauto.
  - destruct (eqb_spec x x0); subst.
    + rewrite update_eq in H.
      injection H as H; subst.
      apply weakening_empty. assumption.
    + apply T_Var.
      rewrite update_neq in H; auto.
  - destruct (eqb_spec x x0); subst; apply T_Abs.
    + rewrite update_shadow in *. assumption.
    + apply IHHt. rewrite update_permute; auto.
Qed.

Theorem preservation : forall t t' T,
  empty |-- t \in T ->
  t --> t' ->
  empty |-- t' \in T.
Proof with eauto.
  intros t t' T HT. generalize dependent t'.
  remember empty as Gamma.
  induction HT; intros t' HE; subst; try solve [inversion HE; subst; auto].
  - (* T_App *)
    inversion HE; subst...
    (* Most of the cases are immediate by induction,
       and eauto takes care of them *)
    + (* ST_AppAbs *)
      apply substitution_preserves_typing with T2...
      inversion HT1...
Qed.

Theorem not_subject_expansion:
  exists t t' T, t --> t' /\ (empty |-- t' \in T) /\ ~ (empty |-- t \in T).
Proof.
  Admitted.
  
Definition stuck (t:tm) : Prop :=
  (normal_form step) t /\ ~ value t.
Corollary type_soundness : forall t t' T,
  empty |-- t \in T ->
  t -->* t' ->
  ~(stuck t').
Proof.
  intros t t' T Hhas_type Hmulti. unfold stuck.
  intros [Hnf Hnot_val]. unfold normal_form in Hnf.
  induction Hmulti.
  - apply progress in Hhas_type.
    destruct Hhas_type as [Hv | He]; auto.
  - apply IHHmulti.
    + apply preservation with (t' := y0) in Hhas_type.
      * assumption.
      * assumption.
    + assumption.
    + assumption.
Qed.

Theorem unique_types : forall Gamma e T T',
  Gamma |-- e \in T ->
  Gamma |-- e \in T' ->
  T = T'.
Proof.
  intros Gamma e T T' H1 H2.
  Admitted.
  
Inductive appears_free_in (x : string) : tm -> Prop :=
  | afi_var : appears_free_in x <{x}>
  | afi_app1 : forall t1 t2,
      appears_free_in x t1 ->
      appears_free_in x <{t1 t2}>
  | afi_app2 : forall t1 t2,
      appears_free_in x t2 ->
      appears_free_in x <{t1 t2}>
  | afi_abs : forall y T1 t1,
      y <> x ->
      appears_free_in x t1 ->
      appears_free_in x <{\y:T1, t1}>
  | afi_if1 : forall t1 t2 t3,
      appears_free_in x t1 ->
      appears_free_in x <{if t1 then t2 else t3}>
  | afi_if2 : forall t1 t2 t3,
      appears_free_in x t2 ->
      appears_free_in x <{if t1 then t2 else t3}>
  | afi_if3 : forall t1 t2 t3,
      appears_free_in x t3 ->
      appears_free_in x <{if t1 then t2 else t3}>.
      
Hint Constructors appears_free_in : core.

Definition closed (t:tm) := forall x, ~ appears_free_in x t.

Lemma free_in_context : forall x t T Gamma,
  appears_free_in x t ->
  Gamma |-- t \in T ->
  exists T', Gamma x = Some T'.
Proof.
  intros x t T Gamma H H0. generalize dependent Gamma.
  generalize dependent T.
  induction H as [| | |y T1 t1 H H0 IHappears_free_in| | |];
         intros.
         (* try solve [inversion H0; eauto]. *)
  - inversion H0. exists T. assumption.
  - inversion H0. apply IHappears_free_in in H4. assumption.
  - inversion H0. apply IHappears_free_in in H6. assumption.
  - inversion H1; subst. apply IHappears_free_in in H7.
    apply update_neq with (A := ty) (m := Gamma) (x1 := x) (x2 := y) (v := T1) in H.
    rewrite -> H in H7. assumption.
  - inversion H0. apply IHappears_free_in in H5. assumption.
  - inversion H0. apply IHappears_free_in in H7. assumption.
  - inversion H0. apply IHappears_free_in in H8. assumption.
Qed.

Corollary typable_empty__closed : forall t T,
  empty |-- t \in T ->
  closed t.
Proof.
  intros t T H x contra.
  apply free_in_context with (T:= T) (Gamma := empty) in contra.
  - solve_by_inverts 2.
  - assumption.
Qed.

Lemma context_invariance : forall Gamma Gamma' t T,
  Gamma |-- t \in T ->
  (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
  Gamma' |-- t \in T.
Proof with eauto.
  intros.
  generalize dependent Gamma'.
  induction H as [| ? x0 ????? | | | |]; intros; auto.
  - apply T_Var. rewrite <- H0.
    + assumption.
    + constructor.
  - apply T_Abs. apply IHhas_type.
    intros x1 Hafi.
    Admitted.
    
Theorem progress_my : forall t T,
  empty |-- t \in T ->
  value t \/ exists t', t --> t'.
Proof. Admitted.

Theorem preservation_my : forall t t' T,
  empty |-- t \in T ->
  t --> t' ->
  empty |-- t' \in T.
Proof. Admitted.
  
Qed.


  
End STLCProp.

