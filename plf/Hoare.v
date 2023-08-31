Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From PLF Require Export Imp.
Set Default Goal Selector "!".

Definition Assertion := state -> Prop.

Module ExAssertions.
Definition assn1 : Assertion := fun st => st X <= st Y.
(* holds for states st in which value of X less or equal of value of Y *)
Definition assn2 : Assertion := fun st => st X = 3 \/ st X <= st Y.
(* holds for states st in which value of X is 3 value of X less or equal of value of Y *)
Definition assn3 : Assertion := fun st => st Z * st Z <= st X /\ ~ (((S (st Z)) * (S (st Z))) <= st X).
(* holds for states st in which value of Z * Z is less of equal than value of X and not sqaure of the number after Z is less or equal than value of X *)
Definition assn4 : Assertion := fun st => st Z = max (st X) (st Y).
(* holds for states st in which value of Z equals max of values X and Y *)
End ExAssertions.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Declare Scope hoare_spec_scope.

Notation "P ->> Q" :=  (assert_implies P Q) (at level 80) : hoare_spec_scope.

Open Scope hoare_spec_scope.

Notation "P <<->> Q" :=  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.

Definition Aexp : Type := state -> nat.
Definition assert_of_Prop (P : Prop) : Assertion := fun _ => P.
Definition Aexp_of_nat (n : nat) : Aexp := fun _ => n.
Definition Aexp_of_aexp (a : aexp) : Aexp := fun st => aeval st a.
Coercion assert_of_Prop : Sortclass >-> Assertion.
Coercion Aexp_of_nat : nat >-> Aexp.
Coercion Aexp_of_aexp : aexp >-> Aexp.
Add Printing Coercion Aexp_of_nat Aexp_of_aexp assert_of_Prop.
Arguments assert_of_Prop /.
Arguments Aexp_of_nat /.
Arguments Aexp_of_aexp /.
Add Printing Coercion Aexp_of_nat Aexp_of_aexp assert_of_Prop.
Declare Scope assertion_scope.
Bind Scope assertion_scope with Assertion.
Bind Scope assertion_scope with Aexp.
Delimit Scope assertion_scope with assertion.
Notation assert P := (P%assertion : Assertion).
Notation mkAexp a := (a%assertion : Aexp).
Notation "~ P" := (fun st => ~ assert P st) : assertion_scope.
Notation "P /\ Q" := (fun st => assert P st /\ assert Q st) : assertion_scope.
Notation "P \/ Q" := (fun st => assert P st \/ assert Q st) : assertion_scope.
Notation "P -> Q" := (fun st => assert P st -> assert Q st) : assertion_scope.
Notation "P <-> Q" := (fun st => assert P st <-> assert Q st) : assertion_scope.
Notation "a = b" := (fun st => mkAexp a st = mkAexp b st) : assertion_scope.
Notation "a <> b" := (fun st => mkAexp a st <> mkAexp b st) : assertion_scope.
Notation "a <= b" := (fun st => mkAexp a st <= mkAexp b st) : assertion_scope.
Notation "a < b" := (fun st => mkAexp a st < mkAexp b st) : assertion_scope.
Notation "a >= b" := (fun st => mkAexp a st >= mkAexp b st) : assertion_scope.
Notation "a > b" := (fun st => mkAexp a st > mkAexp b st) : assertion_scope.
Notation "a + b" := (fun st => mkAexp a st + mkAexp b st) : assertion_scope.
Notation "a - b" := (fun st => mkAexp a st - mkAexp b st) : assertion_scope.
Notation "a * b" := (fun st => mkAexp a st * mkAexp b st) : assertion_scope.

Definition ap {X} (f : nat -> X) (x : Aexp) :=
  fun st => f (x st).

Definition ap2 {X} (f : nat -> nat -> X) (x : Aexp) (y : Aexp) (st : state) :=
  f (x st) (y st).
Module ExamplePrettyAssertions.
Definition ex1 : Assertion := X = 3.
Definition ex2 : Assertion := True.
Definition ex3 : Assertion := False.
Definition assn1 : Assertion := X <= Y.
Definition assn2 : Assertion := X = 3 \/ X <= Y.
Definition assn3 : Assertion := Z = ap2 max X Y.
Definition assn4 : Assertion := Z * Z <= X
                            /\ ~ (((ap S Z) * (ap S Z)) <= X).
End ExamplePrettyAssertions.

Definition hoare_triple (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
    st =[ c ]=> st' -> P st -> Q st'.

Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c custom com at level 99)
  : hoare_spec_scope.
  
Check ({{True}} X := 0 {{True}}).

Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
Proof.
  intros. unfold hoare_triple. intros.
  apply H.
Qed.

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~ (P st)) ->
  {{P}} c {{Q}}.
Proof.
  intros. unfold hoare_triple. intros.
  unfold not in H. apply H in H1. inversion H1.
Qed.

Theorem hoare_skip : forall P, {{P}} skip {{P}}.
Proof.
  intros P st st' H HP. inversion H; subst. apply HP.
Qed.
  
Theorem hoare_seq : forall P Q R c1 c2,
  {{Q}} c2 {{R}} ->
  {{P}} c1 {{Q}} ->
  {{P}} c1; c2 {{R}}.
Proof.
  unfold hoare_triple.
  intros. inversion H1; subst.
  eauto.
Qed.

Definition assn_sub X a (P:Assertion) : Assertion :=
  fun (st : state) =>
    P (X !-> aeval st a ; st).
Notation "P [ X |-> a ]" := (assn_sub X a P)
  (at level 10, X at next level, a custom com) : hoare_spec_scope.
  
Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} X := a {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  unfold assn_sub in HQ.
  assumption.
Qed.

Example assn_sub_example :
  {{(X < 5) [X |-> X + 1]}}
    X := X + 1
  {{X < 5}}.
Proof. apply hoare_asgn. Qed.

Example hoare_asgn_examples1 :
  exists P,
    {{ P }}
      X := 2 * X
    {{ X <= 10 }}.
Proof.
  exists ( (X <= 10) [X |-> 2 * X] ).
  apply hoare_asgn.
Qed.

Example hoare_asgn_examples2 :
  exists P,
    {{ P }}
      X := 3
    {{ 0 <= X /\ X <= 5 }}.
Proof.
  exists ( (0 <= X /\ X <= 5) [X |-> 3]).
  apply hoare_asgn.
Qed.

Theorem hoare_asgn_fwd :
  forall m a P,
  {{fun st => P st /\ st X = m}}
    X := a
  {{fun st => P (X !-> m ; st)
           /\ st X = aeval (X !-> m ; st) a }}.
Proof.
  unfold hoare_triple. intros.
  destruct H0. inversion H; subst.
  split; rewrite t_update_shadow, t_update_same.
  - assumption.
  - reflexivity.
Qed.

Theorem hoare_asgn_fwd_exists :
  forall a P,
  {{fun st => P st}}
    X := a
  {{fun st => exists m, P (X !-> m ; st) /\ st X = aeval (X !-> m ; st) a }}.
Proof.
  unfold hoare_triple. intros.
  exists (st X).
  apply (hoare_asgn_fwd (st X) a P st st').
  - assumption.
  - split.
    + assumption.
    + reflexivity.
Qed.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  unfold hoare_triple, "->>".
  intros P P' Q c Hhoare Himp st st' Heval Hpre.
  apply Hhoare with (st := st).
  - assumption.
  - apply Himp. assumption.
Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  unfold hoare_triple, "->>".
  intros P Q Q' c Hhoare Himp st st' Heval Hpre.
  apply Himp.
  apply Hhoare with (st := st).
  - assumption.
  - assumption.
Qed.

Example hoare_asgn_example1 :
  {{True}} X := 1 {{X = 1}}.
Proof.
  (* WORKED IN CLASS *)
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - unfold "->>", assn_sub, t_update.
    intros st _. simpl. reflexivity.
Qed.

Example assn_sub_example2 :
  {{X < 4}}
    X := X + 1
  {{X < 5}}.
Proof.
  (* WORKED IN CLASS *)
  apply hoare_consequence_pre with (P' := (X < 5) [X |-> X + 1]).
  - apply hoare_asgn.
  - unfold "->>", assn_sub, t_update.
    intros st H. simpl in *. lia.
Qed.

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c Htriple Hpre Hpost.
  apply hoare_consequence_pre with (P' := P').
  - apply hoare_consequence_post with (Q' := Q').
    + assumption.
    + assumption.
  - assumption.
Qed.

Hint Unfold assert_implies hoare_triple assn_sub t_update : core.
Hint Unfold assert_of_Prop Aexp_of_nat Aexp_of_aexp : core.

Theorem hoare_consequence_pre' : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  unfold hoare_triple, "->>".
  intros P P' Q c Hhoare Himp st st' Heval Hpre.
  apply Hhoare with (st := st).
  - assumption.
  - apply Himp. assumption.
Qed.

Theorem hoare_consequence_pre'' : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  auto. (* no progress *)
  Abort.
  
Theorem hoare_consequence_pre''' : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  unfold hoare_triple, "->>".
  intros P P' Q c Hhoare Himp st st' Heval Hpre.
  eapply Hhoare.
  - eassumption.
  - apply Himp. assumption.
Qed.

Theorem hoare_consequence_pre'''' : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  eauto.
Qed.
  
Theorem hoare_consequence_post' : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  eauto.
Qed.

Example hoare_asgn_example1' :
  {{True}} X := 1 {{X = 1}}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - unfold "->>", assn_sub, t_update.
    intros st _. simpl. reflexivity.
Qed.

Example hoare_asgn_example1'' :
  {{True}} X := 1 {{X = 1}}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - auto.
Qed.

Example assn_sub_example2' :
  {{X < 4}}
    X := X + 1
  {{X < 5}}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - auto. (* no progress *)
    unfold "->>", assn_sub, t_update.
    intros st H. simpl in *. lia.
Qed.

Ltac assn_auto :=
  try auto; (* as in example 1, above *)
  try (unfold "->>", assn_sub, t_update;
       intros; simpl in *; lia). (* as in example 2 *)

Example assn_sub_example2'' :
   {{X < 4}}
     X := X + 1
   {{X < 5}}.
Proof.
   eapply hoare_consequence_pre.
   - apply hoare_asgn.
   - assn_auto.
 Qed.
 
Example assn_sub_ex1' :
  {{ X <= 5 }}
     X := 2 * X
  {{ X <= 10 }}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - assn_auto.
Qed.

Example assn_sub_ex2' :
  {{ 0 <= 3 /\ 3 <= 5 }}
    X := 3
  {{ 0 <= X /\ X <= 5 }}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - eauto.
Qed.
  
Example hoare_asgn_example3 : forall (a:aexp) (n:nat),
  {{a = n}}
    X := a;
    skip
  {{X = n}}.
Proof.
  intros a n. eapply hoare_seq.
  - (* right part of seq *)
    apply hoare_skip.
  - (* left part of seq *)
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assn_auto.
Qed.

Example hoare_asgn_example4 :
  {{ True }}
    X := 1;
    Y := 2
  {{ X = 1 /\ Y = 2 }}.
Proof.
  apply hoare_seq with (Q := (X = 1)%assertion).
  (* The annotation %assertion is needed here to help Coq parse correctly. *)
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + simpl. eauto.
  - eapply hoare_consequence_pre.
    + simpl. apply hoare_asgn.
    + simpl. assn_auto.
Qed.

Definition swap_program : com :=
  <{ Z := X; Y := X; X := Z }>.
  
Theorem swap_exercise :
  {{X <= Y}}
    swap_program
  {{Y <= X}}.
Proof.
  eapply hoare_seq.
  - eapply hoare_seq.
    + eapply hoare_asgn.
    + eapply hoare_asgn.
  - eapply hoare_consequence_pre.
    + eapply hoare_asgn.
    + simpl. intros st H. eauto.
Qed.

Lemma helper_for_invalid_triple:
  empty_st =[ X := 3; Y := X ]=> (Y !-> 3; X !-> 3).
Proof.
  apply E_Seq with (st' := (X !-> 3)).
  - constructor. reflexivity.
  - apply E_Asgn. reflexivity.
Qed.

Theorem invalid_triple : ~ forall (a : aexp) (n : nat),
    {{ a = n }}
      X := 3; Y := a
    {{ Y = n }}.
Proof.
  unfold hoare_triple.
  intros H.
  specialize H with (a := X) (n := 0) (st := empty_st) (st' := (X !-> 3; Y !-> 3)).
  simpl in H.
  assert (empty_st =[ X := 3; Y := X ]=> (Y !-> 3; X !-> 3)).
  {
    apply helper_for_invalid_triple.
  }
  
  
  
