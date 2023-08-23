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
  
Qed.
