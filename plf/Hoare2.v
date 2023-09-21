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
  
