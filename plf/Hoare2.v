Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From PLF Require Export Imp.
From PLF Require Import Hoare.
Set Default Goal Selector "!".
Definition FILL_IN_HERE := <{True}>.

(*
  {{ True }}
    if X <= Y then
              {{ True /\ (X <= Y) }} ->>
              {{ Y = X + (Y - X) }}
      Z := Y - X
              {{ Y = X + Z }}
    else
              {{ True /\ ~(X <= Y) }} ->>
              {{ X + Z = X + Z }}
      Y := X + Z
              {{ Y = X + Z }}
    end
  {{ Y = X + Z }}
*)

Definition reduce_to_zero' : com :=
  <{ while X <> 0 do
        X := X - 1
     end }>.

Theorem reduce_to_zero_correct' :
  {{True}}
    reduce_to_zero'
  {{X = 0}}.
Proof.
  unfold reduce_to_zero'.
  eapply hoare_consequence_post.
  - apply hoare_while.
    + eapply hoare_consequence_pre.
      * apply hoare_asgn.
      * unfold assn_sub, "->>". simpl. intros.
        exact I.
  - intros st [Inv GuardFalse].
    unfold bassn in GuardFalse. simpl in GuardFalse.
    rewrite not_true_iff_false in GuardFalse.
    rewrite negb_false_iff in GuardFalse.
    apply eqb_eq in GuardFalse.
    apply GuardFalse.
Qed.

Ltac verify_assn :=
  repeat split;
  simpl;
  unfold assert_implies;
  unfold ap in *; unfold ap2 in *;
  unfold bassn in *; unfold beval in *; unfold aeval in *;
  unfold assn_sub; intros;
  repeat (simpl in *;
          rewrite t_update_eq ||
          (try rewrite t_update_neq;
          [| (intro X; inversion X; fail)]));
  simpl in *;
  repeat match goal with [H : _ /\ _ |- _] =>
                         destruct H end;
  repeat rewrite not_true_iff_false in *;
  repeat rewrite not_false_iff_true in *;
  repeat rewrite negb_true_iff in *;
  repeat rewrite negb_false_iff in *;
  repeat rewrite eqb_eq in *;
  repeat rewrite eqb_neq in *;
  repeat rewrite leb_iff in *;
  repeat rewrite leb_iff_conv in *;
  try subst;
  simpl in *;
  repeat
    match goal with
      [st : state |- _] =>
        match goal with
        | [H : st _ = _ |- _] =>
            rewrite -> H in *; clear H
        | [H : _ = st _ |- _] =>
            rewrite <- H in *; clear H
        end
    end;
  try eauto;
  try lia.

Theorem reduce_to_zero_correct''' :
  {{True}}
    reduce_to_zero'
  {{X = 0}}.
Proof.
  unfold reduce_to_zero'.
  eapply hoare_consequence_post.
  - apply hoare_while.
    + eapply hoare_consequence_pre.
      * apply hoare_asgn.
      * verify_assn.
  - verify_assn.
Qed.

Inductive dcom : Type :=
| DCSkip (Q : Assertion)
  (* skip {{ Q }} *)
| DCSeq (d1 d2 : dcom)
  (* d1 ; d2 *)
| DCAsgn (X : string) (a : aexp) (Q : Assertion)
  (* X := a {{ Q }} *)
| DCIf (b : bexp) (P1 : Assertion) (d1 : dcom)
       (P2 : Assertion) (d2 : dcom) (Q : Assertion)
  (* if b then {{ P1 }} d1 else {{ P2 }} d2 end {{ Q }} *)
| DCWhile (b : bexp) (P : Assertion) (d : dcom)
          (Q : Assertion)
  (* while b do {{ P }} d end {{ Q }} *)
| DCPre (P : Assertion) (d : dcom)
  (* ->> {{ P }} d *)
| DCPost (d : dcom) (Q : Assertion)
  (* d ->> {{ Q }} *).
  
Inductive decorated : Type :=
  | Decorated : Assertion -> dcom -> decorated.
  
Declare Scope dcom_scope.
Notation "'skip' {{ P }}"
      := (DCSkip P)
      (in custom com at level 0, P constr) : dcom_scope.
Notation "l ':=' a {{ P }}"
      := (DCAsgn l a P)
      (in custom com at level 0, l constr at level 0,
          a custom com at level 85, P constr, no associativity) : dcom_scope.
Notation "'while' b 'do' {{ Pbody }} d 'end' {{ Ppost }}"
      := (DCWhile b Pbody d Ppost)
           (in custom com at level 89, b custom com at level 99,
           Pbody constr, Ppost constr) : dcom_scope.
Notation "'if' b 'then' {{ P }} d 'else' {{ P' }} d' 'end' {{ Q }}"
      := (DCIf b P d P' d' Q)
           (in custom com at level 89, b custom com at level 99,
               P constr, P' constr, Q constr) : dcom_scope.
Notation "'->>' {{ P }} d"
      := (DCPre P d)
      (in custom com at level 12, right associativity, P constr) : dcom_scope.
Notation "d '->>' {{ P }}"
      := (DCPost d P)
      (in custom com at level 10, right associativity, P constr) : dcom_scope.
Notation " d ; d' "
      := (DCSeq d d')
      (in custom com at level 90, right associativity) : dcom_scope.
Notation "{{ P }} d"
      := (Decorated P d)
      (in custom com at level 91, P constr) : dcom_scope.
Local Open Scope dcom_scope.
Example dec0 :=
  <{ skip {{ True }} }>.
Example dec1 :=
  <{ while true do {{ True }} skip {{ True }} end
  {{ True }} }>.
  
Set Printing All.
Print dec1.
Unset Printing All.

Example dec_while : decorated :=
  <{
    {{ True }}
      while X <> 0
      do
                {{ True /\ ( X <> 0) }}
        X := X - 1
                {{ True }}
      end
    {{ True /\ X = 0 }} ->> {{ X = 0 }}
  }>.
  
Fixpoint extract (d : dcom) : com :=
  match d with
  | DCSkip _ => CSkip
  | DCSeq d1 d2 => CSeq (extract d1) (extract d2)
  | DCAsgn X a _ => CAsgn X a
  | DCIf b _ d1 _ d2 _ => CIf b (extract d1) (extract d2)
  | DCWhile b _ d _ => CWhile b (extract d)
  | DCPre _ d => extract d
  | DCPost d _ => extract d
  end.
  
Definition extract_dec (dec : decorated) : com :=
  match dec with
  | Decorated P d => extract d
  end.
  
Example extract_while_ex :
  extract_dec dec_while
= <{while X <> 0 do X := X - 1 end}>.
Proof.
  unfold dec_while.
  simpl.
  reflexivity.
Qed.

Definition pre_dec (dec : decorated) : Assertion :=
  match dec with
  | Decorated P d => P
  end.
  
Fixpoint post (d : dcom) : Assertion :=
  match d with
  | DCSkip P => P
  | DCSeq _ d2 => post d2
  | DCAsgn _ _ Q => Q
  | DCIf _ _ _ _ _ Q => Q
  | DCWhile _ _ _ Q => Q
  | DCPre _ d => post d
  | DCPost _ Q => Q
  end.
  
Definition post_dec (dec : decorated) : Assertion :=
  match dec with
  | Decorated P d => post d
  end.
  
Example pre_dec_while : pre_dec dec_while = True.
Proof. reflexivity. Qed.
Example post_dec_while : post_dec dec_while = (X = 0)%assertion.
Proof. reflexivity. Qed.

Definition outer_triple_valid (dec : decorated) :=
  {{pre_dec dec}} extract_dec dec {{post_dec dec}}.
  
Example dec_while_triple_correct :
  outer_triple_valid dec_while
=
  {{ True }}
    while X <> 0 do X := X - 1 end
  {{ X = 0 }}.
Proof. reflexivity. Qed.

Fixpoint verification_conditions (P : Assertion) (d : dcom) : Prop :=
  match d with
  | DCSkip Q =>
      (P ->> Q)
  | DCSeq d1 d2 =>
      verification_conditions P d1
      /\ verification_conditions (post d1) d2
  | DCAsgn X a Q =>
      (P ->> Q [X |-> a])
  | DCIf b P1 d1 P2 d2 Q =>
      ((P /\ b) ->> P1)%assertion
      /\ ((P /\ ~ b) ->> P2)%assertion
      /\ (post d1 ->> Q) /\ (post d2 ->> Q)
      /\ verification_conditions P1 d1
      /\ verification_conditions P2 d2
  | DCWhile b Pbody d Ppost =>
      (* post d is the loop invariant and the initial
         precondition *)
      (P ->> post d)
      /\ ((post d /\ b) ->> Pbody)%assertion
      /\ ((post d /\ ~ b) ->> Ppost)%assertion
      /\ verification_conditions Pbody d
  | DCPre P' d =>
      (P ->> P')
      /\ verification_conditions P' d
  | DCPost d Q =>
      verification_conditions P d
      /\ (post d ->> Q)
  end.
  
Theorem verification_correct : forall d P,
  verification_conditions P d -> {{P}} extract d {{post d}}.
Proof.
  induction d; intros; simpl in *.
  - (* Skip *)
    eapply hoare_consequence_pre.
      + apply hoare_skip.
      + assumption.
  - (* Seq *)
    destruct H as [H1 H2].
    eapply hoare_seq.
      + apply IHd2. apply H2.
      + apply IHd1. apply H1.
  - (* Asgn *)
    eapply hoare_consequence_pre.
      + apply hoare_asgn.
      + assumption.
  - (* If *)
    destruct H as [HPre1 [HPre2 [Hd1 [Hd2 [HThen HElse] ] ] ] ].
    apply IHd1 in HThen. clear IHd1.
    apply IHd2 in HElse. clear IHd2.
    apply hoare_if.
      + eapply hoare_consequence; eauto.
      + eapply hoare_consequence; eauto.
  - (* While *)
    destruct H as [Hpre [Hbody1 [Hpost1 Hd] ] ].
    eapply hoare_consequence; eauto.
    apply hoare_while.
    eapply hoare_consequence_pre; eauto.
  - (* Pre *)
    destruct H as [HP Hd].
    eapply hoare_consequence_pre; eauto.
  - (* Post *)
    destruct H as [Hd HQ].
    eapply hoare_consequence_post; eauto.
Qed.

Definition verification_conditions_dec
              (dec : decorated) : Prop :=
  match dec with
  | Decorated P d => verification_conditions P d
  end.
Corollary verification_correct_dec : forall dec,
  verification_conditions_dec dec ->
  outer_triple_valid dec.
Proof.
  intros [P d]. apply verification_correct.
Qed.


  
