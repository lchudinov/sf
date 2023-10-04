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

Eval simpl in verification_conditions_dec dec_while.
Example vc_dec_while: verification_conditions_dec dec_while.
Proof. verify_assn. Qed.

Ltac verify :=
  intros;
  apply verification_correct;
  verify_assn.
  
Theorem dec_while_correct :
  outer_triple_valid dec_while.
Proof. verify. Qed.

Definition swap_dec (m n : nat) : decorated :=
  <{
    {{ X = m /\ Y = n }} ->>
      {{ (X + Y) - ((X + Y) - Y) = n /\ (X + Y) - Y = m }}
    X := X + Y
      {{ X - (X - Y) = n /\ X - Y = m }};
    Y := X - Y
      {{ X - Y = n /\ Y = m }};
    X := X - Y
    {{ X = n /\ Y = m}}
  }>.
Theorem swap_correct : forall m n,
  outer_triple_valid (swap_dec m n).
Proof. verify. Qed.

Definition positive_difference_dec :=
  <{
    {{True}}
    if X <= Y then
          {{True /\ X <= Y}} ->>
          {{(Y - X) + X = Y
                   \/ (Y - X) + Y = X}}
      Z := Y - X
          {{Z + X = Y \/ Z + Y = X}}
    else
          {{True /\ ~(X <= Y)}} ->>
          {{(X - Y) + X = Y
                   \/ (X - Y) + Y = X}}
      Z := X - Y
          {{Z + X = Y \/ Z + Y = X}}
    end
    {{Z + X = Y \/ Z + Y = X}}
  }>.
Theorem positive_difference_correct :
  outer_triple_valid positive_difference_dec.
Proof. verify. Qed.

Definition if_minus_plus_dec :=
  <{
  {{True}}
  if (X <= Y) then
              {{ True /\ X <= Y }} ->>
              {{ Y = X + (Y - X) }}
    Z := Y - X
              {{ Y = X + Z }}
  else
              {{ True /\ ~(X <= Y) }} ->>
              {{ X + Z = X + Z }}
    Y := X + Z
              {{ Y = X + Z }}
  end
  {{ Y = X + Z }} }>.
Theorem if_minus_plus_correct :
  outer_triple_valid if_minus_plus_dec.
Proof. verify. Qed.

Definition div_mod_dec (a b : nat) : decorated :=
  <{
  {{ True }} ->>
  {{ FILL_IN_HERE }}
    X := a
             {{ FILL_IN_HERE }};
    Y := 0
             {{ FILL_IN_HERE }};
    while b <= X do
             {{ FILL_IN_HERE }} ->>
             {{ FILL_IN_HERE }}
      X := X - b
             {{ FILL_IN_HERE }};
      Y := Y + 1
             {{ FILL_IN_HERE }}
    end
  {{ FILL_IN_HERE }} ->>
  {{ FILL_IN_HERE }} }>.
Theorem div_mod_outer_triple_valid : forall a b,
  outer_triple_valid (div_mod_dec a b).
Proof. Admitted.

Example subtract_slowly_dec (m : nat) (p : nat) : decorated :=
  <{
  {{ X = m /\ Z = p }} ->>
  {{ Z - X = p - m }}
    while X <> 0 do
                  {{ Z - X = p - m /\ X <> 0 }} ->>
                  {{ (Z - 1) - (X - 1) = p - m }}
       Z := Z - 1
                  {{ Z - (X - 1) = p - m }} ;
       X := X - 1
                  {{ Z - X = p - m }}
    end
  {{ Z - X = p - m /\ X = 0 }} ->>
  {{ Z = p - m }} }>.
  
Theorem subtract_slowly_outer_triple_valid : forall m p,
  outer_triple_valid (subtract_slowly_dec m p).
Proof. verify. Qed.

Example slow_assignment_dec (m : nat) : decorated :=
  <{
    {{ X = m }}
      Y := 0
                    {{ X = m /\ Y = 0 }} ->>
                    {{ X + Y = m }} ;
      while X <> 0 do
                    {{ X + Y = m /\ (X <> 0) }} ->>
                    {{ (X - 1) + (Y + 1) = m }}
         X := X - 1
                    {{ X + (Y + 1) = m }} ;
         Y := Y + 1
                    {{ X + Y = m }}
      end
    {{ X + Y = m /\ ~(X <> 0) }} ->>
    {{ Y = m }}
  }>.

Theorem slow_assignment : forall m,
  outer_triple_valid (slow_assignment_dec m).
Proof. verify. Qed.

Fixpoint parity x :=
  match x with
  | 0 => 0
  | 1 => 1
  | S (S x') => parity x'
  end.
  
Definition parity_dec (m:nat) : decorated :=
  <{
  {{ X = m }} ->>
  {{ ap parity X = parity m }}
    while 2 <= X do
                  {{ ap parity X = parity m /\ X <= 2 }} ->>
                  {{ ap parity (X - 2) = parity m }}
      X := X - 2
                  {{ ap parity X = parity m }}
    end
  {{ ap parity X = parity m /\ ~(2 <= X) }} ->>
  {{ X = parity m }} }>.
  
Lemma parity_ge_2 : forall x,
  2 <= x -> parity (x - 2) = parity x.
Proof.
  destruct x; intros; simpl.
  - reflexivity.
  - destruct x; simpl.
    + lia.
    + rewrite sub_0_r. reflexivity.
Qed.

Lemma parity_lt_2 : forall x,
  ~ 2 <= x -> parity x = x.
Proof.
  induction x; intros; simpl.
  - reflexivity.
  - destruct x.
    + reflexivity.
    + lia.
Qed.

Theorem parity_outer_triple_valid : forall m,
  outer_triple_valid (parity_dec m).
Proof.
  verify.
  Admitted.

Definition sqrt_dec (m:nat) : decorated :=
  <{
    {{ X = m }} ->>
    {{ X = m /\ 0 * 0 <= m }}
      Z := 0
                   {{ X = m /\ Z * Z <= m }};
      while ((Z+1)*(Z+1) <= X) do
                   {{ X = m /\ Z * Z <= m /\ ((Z + 1)*(Z + 1) <= X) }} ->>
                   {{ X = m /\ (Z + 1) * (Z + 1) <= m }}
        Z := Z + 1
                   {{ X = m /\ Z * Z <= m }}
      end
    {{ X = m /\ Z * Z <= m /\ ~((Z + 1)*(Z + 1) <= X) }} ->>
    {{ Z*Z <= m /\ m < (Z+1)*(Z+1) }}
  }>.
Theorem sqrt_correct : forall m,
  outer_triple_valid (sqrt_dec m).
Proof. verify. Qed.

Definition sqr_dec (m : nat) : decorated :=
<{
  {{ X = m }} ->>
  {{ 0 = 0*m /\ X = m }}
    Y := 0
                  {{ 0 = Y*m /\ X = m }};
    Z := 0
                  {{ Z = Y*m /\ X = m }};
    while Y <> X do
                  {{ Z = Y*m /\ X = m /\ Y <> X }} ->>
                  {{ Z+X = (Y+1)*m /\ X = m }}
      Z := Z + X
                  {{ Z = (Y+1)*m /\ X = m }};
      Y := Y + 1
                  {{ Z = Y*m /\ X = m }}
    end
  {{ Z = Y*m /\ X = m /\ ~(Y <> X) }} ->>
  {{ Z = m*m }}
}>.

Theorem sqr_correct : forall m,
  outer_triple_valid (sqr_dec m).
Proof. verify. Qed.

Fixpoint fact (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => n * (fact n')
  end.

Definition factorial_dec (m : nat) : decorated :=
  <{
    {{ X = m }} ->>
      {{ 1 * 1 = ap fact 1 }}
      Z := 1
          {{ Z * 1 = ap fact Z }};
      Y := 1
            {{ Z * Y = ap fact Z }} ;
      while Z <= X do
                    {{ Z * Y = ap fact Z /\ (Z <= X) }} ->>
                    {{ (1 + Z) * Z * Y  = ap fact (1 + Z) }}
         Y := Z * Y
                    {{ (1 + Z) * Y  = ap fact (1 + Z) }} ;
         Z := 1 + Z
                    {{ Z * Y = ap fact Z }}
      end
    {{ Z * Y = ap fact Z /\ ~(Z <= X) }} ->>
    {{ Y = fact m }}
  }>.
  
Theorem factorial_correct: forall m,
  outer_triple_valid (factorial_dec m).
Proof.
  verify.
  Admitted.
  
Definition minimum_dec (a b : nat) : decorated :=
  <{
    {{ True }} ->>
    {{ ap2 min a b + 0 = ap2 min a b }}
      X := a
             {{ ap2 min X b + 0 = ap2 min a b }};
      Y := b
             {{ ap2 min X Y + 0 = ap2 min a b }};
      Z := 0
             {{ ap2 min X Y + Z = ap2 min a b }};
      while X <> 0 && Y <> 0 do
             {{ ap2 min X Y + Z = ap2 min a b /\ (X <> 0 /\ Y > 0) }} ->>
             {{ ap2 min (X - 1) (Y - 1) + (Z + 1) = ap2 min a b }}
        X := X - 1
             {{ ap2 min X (Y - 1) + (Z + 1) = ap2 min a b }};
        Y := Y - 1
             {{ ap2 min X Y + (Z + 1) = ap2 min a b }};
        Z := Z + 1
             {{ ap2 min X Y + Z = ap2 min a b  }}
      end
    {{  ap2 min X Y + Z = ap2 min a b /\ ~(X <> 0 /\ Y <> 0) }} ->>
    {{ Z = min a b }}
  }>.
Theorem minimum_correct : forall a b,
  outer_triple_valid (minimum_dec a b).
Proof. intros a b. verify. Admitted.

Definition two_loops_dec (a b c : nat) : decorated :=
  <{
    {{ True }} ->>
    {{ c = 0 + c /\ 0 = 0 }}
      X := 0
                   {{ c = X + c /\ 0 = 0}};
      Y := 0
                   {{ c = X + c /\ Y = 0}};
      Z := c
                   {{ Z = X + c /\ Y = 0 }};
      while X <> a do
                   {{ Z = X + c /\ Y = 0 /\ (X <> a) }} ->>
                   {{ (Z + 1) = (X + 1) + c /\ Y = 0}}
        X := X + 1
                   {{ (Z + 1) = X + c /\ Y = 0}};
        Z := Z + 1
                   {{ Z = X + c /\ Y = 0 }}
      end
                   {{ Z = X + c /\ Y = 0 /\ ~(X <> a) }} ->>
                   {{ Z = a +  Y + c }};
      while Y <> b do
                   {{ Z = a + Y + c /\ (Y <> b) }} ->>
                   {{ Z + 1 = a + (Y + 1) + c }}
        Y := Y + 1
                   {{ Z + 1 = a + Y + c }};
        Z := Z + 1
                   {{ Z = a + Y + c }}
      end
    {{ Z = a + Y + c  /\ ~(Y <> b)}} ->>
    {{ Z = a + b + c }}
  }>.
Theorem two_loops : forall a b c,
  outer_triple_valid (two_loops_dec a b c).
Proof. intros a b c. verify.
Qed.

Fixpoint pow2 n :=
  match n with
  | 0 => 1
  | S n' => 2 * (pow2 n')
  end.
Definition dpow2_dec (n : nat) :=
  <{
    {{ True }} ->>
    {{ 1 = pow2 (0 + 1) - 1 /\ 1 = pow2 0 }}
      X := 0
               {{ 1 = ap pow2 (X + 1) - 1 /\ 1 = ap pow2 X }};
      Y := 1
               {{ Y = ap pow2 (X + 1) - 1 /\ 1 = ap pow2 X }};
      Z := 1
               {{ Y = ap pow2 (X + 1) - 1 /\ Z = ap pow2 X }};
      while X <> n do
               {{ Y = ap pow2 (X + 1) - 1 /\ Z = ap pow2 X /\ (X <> n) }} ->>
               {{  (Y + (2 * Z)) = ap pow2 ((X + 1) + 1) - 1 /\ 2 * Z = ap pow2 (X + 1) }}
        Z := 2 * Z
               {{ (Y + Z) = ap pow2 ((X + 1) + 1) - 1 /\ Z = ap pow2 (X + 1) }};
        Y := Y + Z
               {{ Y = ap pow2 ((X + 1) + 1) - 1 /\ Z = ap pow2 (X + 1) }};
        X := X + 1
               {{ Y = ap pow2 (X + 1) - 1 /\ Z = ap pow2 X }}
      end
    {{ Y = ap pow2 (X + 1) - 1 /\ Z = ap pow2 X /\ ~(X <> n) }} ->>
    {{ Y = ap pow2 (n+1) - 1 }}
  }>.
Lemma pow2_plus_1 : forall n,
  pow2 (n+1) = pow2 n + pow2 n.
Proof.
  induction n; simpl.
  - reflexivity.
  - lia.
Qed.
Lemma pow2_le_1 : forall n, pow2 n >= 1.
Proof.
  induction n; simpl; [constructor | lia].
Qed.
Theorem dpow2_down_correct : forall n,
  outer_triple_valid (dpow2_dec n).
Proof.
  intros n.
  verify.
  - rewrite pow2_plus_1. 
Admitted.

Definition is_wp P c Q :=
  {{P}} c {{Q}} /\
  forall P', {{P'}} c {{Q}} -> (P' ->> P).

(*
1) {{ X = 5 }}  skip  {{ X = 5 }}

2) {{ Y + Z = 5 }}  X := Y + Z {{ X = 5 }}

3) {{ True }}  X := Y  {{ X = Y }}

4) {{ X = 0 /\ Z = 4 \/ X <> 0 /\ W = 3 }}
   if X = 0 then Y := Z + 1 else Y := W + 2 end
   {{ Y = 5 }}

5) {{ False }}
   X := 5
   {{ X = 0 }}

6) {{ False }}
    while true do X := 0 end
    {{ X = 0 }}
*)

Theorem is_wp_example :
  is_wp (Y <= 4) <{X := Y + 1}> (X <= 5).
Proof.
  unfold is_wp.
  split; unfold hoare_triple; intros.
  Admitted.

Theorem hoare_asgn_weakest : forall Q X a,
  is_wp (Q [X |-> a]) <{ X := a }> Q.
Proof. Admitted.

Fixpoint fib n :=
  match n with
  | 0 => 1
  | S n' => match n' with
            | 0 => 1
            | S n'' => fib n' + fib n''
            end
  end.
  
Lemma fib_eqn : forall n,
  n > 0 ->
  fib n + fib (pred n) = fib (1 + n).
Proof.
  intros.
  induction n.
  - inversion H.
  - 
  Admitted.
  
Definition T : string := "T".
Definition dfib (n : nat) : decorated :=
  <{
    {{ True }} ->>
    {{ FILL_IN_HERE }}
    X := 1
                {{ FILL_IN_HERE }} ;
    Y := 1
                {{ FILL_IN_HERE }} ;
    Z := 1
                {{ FILL_IN_HERE }} ;
    while X <> 1 + n do
                  {{  FILL_IN_HERE /\ (X <> 1 + n) }} ->>
                  {{ FILL_IN_HERE }}
      T := Z
                  {{ FILL_IN_HERE }};
      Z := Z + Y
                  {{ FILL_IN_HERE }};
      Y := T
                  {{ FILL_IN_HERE }};
      X := 1 + X
                  {{ FILL_IN_HERE }}
    end
    {{ FILL_IN_HERE /\ ~(X <> 1 + n) }} ->>
    {{ Y = fib n }}
   }>.

