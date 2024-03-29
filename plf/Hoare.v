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
  specialize H with (a := X) (n := 0) (st := empty_st).
  simpl in H.
  assert (empty_st =[ X := 3; Y := X ]=> (Y !-> 3; X !-> 3)).
  {
    apply helper_for_invalid_triple.
  }
  apply H in H0.
  - inversion H0.
  - reflexivity.
Qed.

Definition bassn b : Assertion :=
  fun st => (beval st b = true).
  
Coercion bassn : bexp >-> Assertion.
Arguments bassn /.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassn b) st).
Proof.
  congruence.
Qed.

Hint Resolve bexp_eval_false : core.

Theorem hoare_if : forall P Q (b:bexp) c1 c2,
  {{ P /\ b }} c1 {{Q}} ->
  {{ P /\ ~ b}} c2 {{Q}} ->
  {{P}} if b then c1 else c2 end {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst; eauto.
Qed.

Example if_example :
  {{ True }}
    if (X = 0)
      then Y := 2
      else Y := X + 1
    end
  {{ X <= Y }}.
Proof.
  apply hoare_if.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assn_auto. (* no progress*)
      unfold "->>", assn_sub, t_update, bassn.
      simpl. intros st [_ H].
      apply eqb_eq in H.
      rewrite H. lia.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assn_auto.
Qed.

Ltac assn_auto' :=
  unfold "->>", assn_sub, t_update, bassn;
  intros; simpl in *;
  try rewrite -> eqb_eq in *; (* for equalities *)
  auto; try lia.
  
Example if_example'' :
  {{ True }}
    if (X = 0)
      then Y := 2
      else Y := X + 1
    end
  {{ X <= Y }}.
Proof.
  apply hoare_if.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assn_auto'.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assn_auto'.
Qed.

Example if_example''' :
  {{ True }}
    if (X = 0)
      then Y := 2
      else Y := X + 1
    end
  {{ X <= Y }}.
Proof.
  apply hoare_if; eapply hoare_consequence_pre;
  try apply hoare_asgn; try assn_auto'.
Qed.

Ltac assn_auto'' :=
  unfold "->>", assn_sub, t_update, bassn;
  intros; simpl in *;
  try rewrite -> eqb_eq in *; (* for equalities *)
  try rewrite -> leb_le in *; (* for inequalities *)
  auto; try lia.

Theorem if_minus_plus :
  {{True}}
    if (X <= Y)
      then Z := Y - X
      else Y := X + Z
    end
  {{Y = X + Z}}.
Proof.
  apply hoare_if;
  eapply hoare_consequence_pre;
  simpl; try apply hoare_asgn; assn_auto''.
Qed.

Module If1.
Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CIf1 : bexp -> com -> com.
Notation "'if1' x 'then' y 'end'" :=
         (CIf1 x y)
             (in custom com at level 0, x custom com at level 99).
Notation "'skip'" :=
         CSkip (in custom com at level 0).
Notation "x := y" :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity).
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity).
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99).
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99).
            
Reserved Notation "st '=[' c ']=>'' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).
Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st =[ c1 ]=> st' ->
      st' =[ c2 ]=> st'' ->
      st =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st =[ while b do c end ]=> st''
  | E_If1True : forall st st' b c,
      beval st b = true ->
      st =[ c ]=> st' ->
      st =[ if1 b then c end ]=> st'
  | E_If1False : forall st b c,
      beval st b = false ->
      st =[ if1 b then c end ]=> st

where "st '=[' c ']=>' st'" := (ceval c st st').
Hint Constructors ceval : core.

Example if1true_test :
  empty_st =[ if1 X = 0 then X := 1 end ]=> (X !-> 1).
Proof. eauto. Qed.
Example if1false_test :
  (X !-> 2) =[ if1 X = 0 then X := 1 end ]=> (X !-> 2).
Proof. eauto. Qed.

Definition hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
       st =[ c ]=> st' ->
       P st ->
       Q st'.
Hint Unfold hoare_triple : core.
Notation "{{ P }} c {{ Q }}" := (hoare_triple P c Q)
                                  (at level 90, c custom com at level 99)
                                  : hoare_spec_scope.
                                  
Theorem hoare_if1 : forall P Q (b:bexp) c,
  {{ P /\ b }} c {{Q}} ->
  (P /\ ~ (bassn b))%assertion ->> Q  ->
  {{P}} if1 b then c end {{Q}}.
Proof.
    intros P Q b c1 HTrue HFalse st st' HE HP.
    inversion HE; subst; eauto.
Qed.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  eauto.
Qed.
Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} (X := a) {{Q}}.
Proof.
  intros Q X a st st' Heval HQ.
  inversion Heval; subst.
  auto.
Qed.

Ltac assn_auto''' :=
  unfold "->>", assn_sub, t_update, bassn;
  intros; simpl in *;
  try rewrite -> eqb_eq in *; (* for equalities *)
  try rewrite -> leb_le in *; (* for inequalities *)
  auto; try lia.

Lemma hoare_if1_good:
  {{ X + Y = Z }}
  if1 Y <> 0 then
    X := X + Y
  end
  {{ X = Z }}.
Proof.
  apply hoare_if1.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + intros st [H _]. simpl in *. assumption.
  - intros st [H1 H2]. simpl in *.
    destruct (st Y =? 0) eqn:EqnY.
    + simpl in *. rewrite eqb_eq in *.
      rewrite <- H1. rewrite EqnY. eauto.
    + simpl in *. contradiction.
Qed.

End If1.

Theorem hoare_while : forall P (b:bexp) c,
  {{P /\ b}} c {{P}} ->
  {{P}} while b do c end {{P /\ ~ b}}.
Proof.
  intros P b c Hhoare st st' Heval HP.
  (* We proceed by induction on Heval, because, in the "keep looping" case,
     its hypotheses talk about the whole loop instead of just c. The
     remember is used to keep the original command in the hypotheses;
     otherwise, it would be lost in the induction. By using inversion
     we clear away all the cases except those involving while. *)
  remember <{while b do c end}> as original_command eqn:Horig.
  induction Heval;
    try (inversion Horig; subst; clear Horig);
    eauto.
Qed.

Example while_example :
  {{X <= 3}}
    while (X <= 2) do
      X := X + 1
    end
  {{X = 3}}.
Proof.
  eapply hoare_consequence_post.
  - apply hoare_while.
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assn_auto''.
  - assn_auto''.
Qed.

Theorem always_loop_hoare : forall Q,
  {{True}} while true do skip end {{Q}}.
Proof.
  intros Q.
  eapply hoare_consequence_post.
  - apply hoare_while. apply hoare_post_true. auto.
  - simpl. intros st [Hinv Hguard]. congruence.
Qed.

Module RepeatExercise.
Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CRepeat : com -> bexp -> com.

Notation "'repeat' e1 'until' b2 'end'" :=
          (CRepeat e1 b2)
              (in custom com at level 0,
               e1 custom com at level 99, b2 custom com at level 99).
Notation "'skip'" :=
         CSkip (in custom com at level 0).
Notation "x := y" :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity).
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity).
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99).
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99).

Inductive ceval : state -> com -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st =[ c1 ]=> st' ->
      st' =[ c2 ]=> st'' ->
      st =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st =[ while b do c end ]=> st''
  | E_RepeatFalse : forall b st st' c,
      beval st b = false ->
      st =[ c ]=> st' ->
      st =[ repeat c until b end ]=> st'
  | E_RepeatTrue : forall st st' st'' b c,
      beval st b = true ->
      st =[ c ]=> st' ->
      st' =[ repeat c until b end ]=> st'' ->
      st =[ repeat c until b end ]=> st''

where "st '=[' c ']=>' st'" := (ceval st c st').

Definition hoare_triple (P : Assertion) (c : com) (Q : Assertion): Prop :=
  forall st st', st =[ c ]=> st' -> P st -> Q st'.
Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c custom com at level 99).

Definition ex1_repeat :=
  <{ repeat
       X := 1;
       Y := Y + 1
     until (X = 1) end }>.
Theorem ex1_repeat_works :
  empty_st =[ ex1_repeat ]=> (Y !-> 1 ; X !-> 1).
Proof.
  unfold ex1_repeat.
  apply E_RepeatFalse.
  + eauto.
  + apply E_Seq with (st' := (X !-> 1)).
    * apply E_Asgn. reflexivity.
    * apply E_Asgn. reflexivity.
Qed.

Theorem hoare_repeat : forall P Q (b:bexp) c,
  {{P}} c {{Q}} ->
  (Q /\ ~ (bassn b))%assertion ->> P  ->
  {{P}} repeat c until b end {{Q /\ (bassn b)}}.
Proof.
  intros P Q b c Hhoare Qnb st' st'' Heval HP.
  (* We proceed by induction on Heval, because, in the "keep looping" case,
     its hypotheses talk about the whole loop instead of just c. The
     remember is used to keep the original command in the hypotheses;
     otherwise, it would be lost in the induction. By using inversion
     we clear away all the cases except those involving while. *)
  remember <{repeat c until b end}> as original_command eqn:Horig.
  
  induction Heval;
    try (inversion Horig; subst; clear Horig);
    eauto; split.
    Admitted.

Example hoare_repeat_ex:
  {{ X > 0 }}
    repeat
      Y := X;
      X := X - 1
    until X = 0 end
  {{ X = 0 /\ Y > 0 }}.
Proof.
  Admitted.

End RepeatExercise.

Module Himp.
Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : string -> com.
Notation "'havoc' l" := (CHavoc l)
                          (in custom com at level 60, l constr at level 0).
Notation "'skip'" :=
         CSkip (in custom com at level 0).
Notation "x := y" :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity).
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity).
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99).
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99).
Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st =[ c1 ]=> st' ->
      st' =[ c2 ]=> st'' ->
      st =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st =[ while b do c end ]=> st''
  | E_Havoc : forall st x n,
      st =[ havoc x ]=> (x !-> n ; st)

where "st '=[' c ']=>' st'" := (ceval c st st').
Hint Constructors ceval : core.

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st', st =[ c ]=> st' -> P st -> Q st'.
Hint Unfold hoare_triple : core.
Notation "{{ P }} c {{ Q }}" := (hoare_triple P c Q)
                                  (at level 90, c custom com at level 99)
                                  : hoare_spec_scope.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof. eauto. Qed.

Definition havoc_pre (X : string) (Q : Assertion) (st : total_map nat) : Prop
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
Theorem hoare_havoc : forall (Q : Assertion) (X : string),
  {{ havoc_pre X Q }} havoc X {{ Q }}.
Proof.
  (* FILL IN HERE *) Admitted.

End Himp.

(* ================================================================= *)
(** ** Assert and Assume *)

(** **** Exercise: 4 stars, standard (assert_vs_assume)

    In this exercise, we will extend IMP with two commands, [assert]
    and [assume]. Both commands are ways to indicate that a certain
    statement should hold any time this part of the program is
    reached. However they differ as follows:

    - If an [assert] statement fails, it causes the program to go into
      an error state and exit.

    - If an [assume] statement fails, the program fails to evaluate at
      all. In other words, the program gets stuck and has no final
      state.

    The new set of commands is: *)

    Module HoareAssertAssume.

    Inductive com : Type :=
      | CSkip : com
      | CAsgn : string -> aexp -> com
      | CSeq : com -> com -> com
      | CIf : bexp -> com -> com -> com
      | CWhile : bexp -> com -> com
      | CAssert : bexp -> com
      | CAssume : bexp -> com.
    
    Notation "'assert' l" := (CAssert l)
                               (in custom com at level 8, l custom com at level 0).
    Notation "'assume' l" := (CAssume l)
                              (in custom com at level 8, l custom com at level 0).
    Notation "'skip'"  :=
             CSkip (in custom com at level 0).
    Notation "x := y"  :=
             (CAsgn x y)
                (in custom com at level 0, x constr at level 0,
                 y at level 85, no associativity).
    Notation "x ; y" :=
             (CSeq x y)
               (in custom com at level 90, right associativity).
    Notation "'if' x 'then' y 'else' z 'end'" :=
             (CIf x y z)
               (in custom com at level 89, x at level 99,
                y at level 99, z at level 99).
    Notation "'while' x 'do' y 'end'" :=
             (CWhile x y)
                (in custom com at level 89, x at level 99, y at level 99).
    
    (** To define the behavior of [assert] and [assume], we need to add
        notation for an error, which indicates that an assertion has
        failed. We modify the [ceval] relation, therefore, so that
        it relates a start state to either an end state or to [error].
        The [result] type indicates the end value of a program,
        either a state or an error: *)
    
    Inductive result : Type :=
      | RNormal : state -> result
      | RError : result.
    
    (** Now we are ready to give you the ceval relation for the new language. *)
    
    Inductive ceval : com -> state -> result -> Prop :=
      (* Old rules, several modified *)
      | E_Skip : forall st,
          st =[ skip ]=> RNormal st
      | E_Asgn  : forall st a1 n x,
          aeval st a1 = n ->
          st =[ x := a1 ]=> RNormal (x !-> n ; st)
      | E_SeqNormal : forall c1 c2 st st' r,
          st  =[ c1 ]=> RNormal st' ->
          st' =[ c2 ]=> r ->
          st  =[ c1 ; c2 ]=> r
      | E_SeqError : forall c1 c2 st,
          st =[ c1 ]=> RError ->
          st =[ c1 ; c2 ]=> RError
      | E_IfTrue : forall st r b c1 c2,
          beval st b = true ->
          st =[ c1 ]=> r ->
          st =[ if b then c1 else c2 end ]=> r
      | E_IfFalse : forall st r b c1 c2,
          beval st b = false ->
          st =[ c2 ]=> r ->
          st =[ if b then c1 else c2 end ]=> r
      | E_WhileFalse : forall b st c,
          beval st b = false ->
          st =[ while b do c end ]=> RNormal st
      | E_WhileTrueNormal : forall st st' r b c,
          beval st b = true ->
          st  =[ c ]=> RNormal st' ->
          st' =[ while b do c end ]=> r ->
          st  =[ while b do c end ]=> r
      | E_WhileTrueError : forall st b c,
          beval st b = true ->
          st =[ c ]=> RError ->
          st =[ while b do c end ]=> RError
      (* Rules for Assert and Assume *)
      | E_AssertTrue : forall st b,
          beval st b = true ->
          st =[ assert b ]=> RNormal st
      | E_AssertFalse : forall st b,
          beval st b = false ->
          st =[ assert b ]=> RError
      | E_Assume : forall st b,
          beval st b = true ->
          st =[ assume b ]=> RNormal st
    
    where "st '=[' c ']=>' r" := (ceval c st r).
    
    (** We redefine hoare triples: Now, [{{P}} c {{Q}}] means that,
        whenever [c] is started in a state satisfying [P], and terminates
        with result [r], then [r] is not an error and the state of [r]
        satisfies [Q]. *)
    
    Definition hoare_triple
               (P : Assertion) (c : com) (Q : Assertion) : Prop :=
      forall st r,
         st =[ c ]=> r  -> P st  ->
         (exists st', r = RNormal st' /\ Q st').
    
    Notation "{{ P }}  c  {{ Q }}" :=
      (hoare_triple P c Q) (at level 90, c custom com at level 99)
      : hoare_spec_scope.
    
    (** To test your understanding of this modification, give an example
        precondition and postcondition that are satisfied by the [assume]
        statement but not by the [assert] statement. *)
    
    Theorem assert_assume_differ : exists (P:Assertion) b (Q:Assertion),
           ({{P}} assume b {{Q}})
      /\ ~ ({{P}} assert b {{Q}}).
    (* FILL IN HERE *) Admitted.
    
    (** Then prove that any triple for an [assert] also works when
        [assert] is replaced by [assume]. *)
    
    Theorem assert_implies_assume : forall P b Q,
         ({{P}} assert b {{Q}})
      -> ({{P}} assume b {{Q}}).
    Proof.
    (* FILL IN HERE *) Admitted.
    
    (** Next, here are proofs for the old hoare rules adapted to the new
        semantics.  You don't need to do anything with these. *)
    
    Theorem hoare_asgn : forall Q X a,
      {{Q [X |-> a]}} X := a {{Q}}.
    Proof.
      unfold hoare_triple.
      intros Q X a st st' HE HQ.
      inversion HE. subst.
      exists (X !-> aeval st a ; st). split; try reflexivity.
      assumption. Qed.
    
    Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
      {{P'}} c {{Q}} ->
      P ->> P' ->
      {{P}} c {{Q}}.
    Proof.
      intros P P' Q c Hhoare Himp.
      intros st st' Hc HP. apply (Hhoare st st').
      - assumption.
      - apply Himp. assumption. Qed.
    
    Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
      {{P}} c {{Q'}} ->
      Q' ->> Q ->
      {{P}} c {{Q}}.
    Proof.
      intros P Q Q' c Hhoare Himp.
      intros st r Hc HP.
      unfold hoare_triple in Hhoare.
      assert (exists st', r = RNormal st' /\ Q' st').
      { apply (Hhoare st); assumption. }
      destruct H as [st' [Hr HQ'] ].
      exists st'. split; try assumption.
      apply Himp. assumption.
    Qed.
    
    Theorem hoare_seq : forall P Q R c1 c2,
      {{Q}} c2 {{R}} ->
      {{P}} c1 {{Q}} ->
      {{P}} c1;c2 {{R}}.
    Proof.
      intros P Q R c1 c2 H1 H2 st r H12 Pre.
      inversion H12; subst.
      - eapply H1.
        + apply H6.
        + apply H2 in H3. apply H3 in Pre.
            destruct Pre as [st'0 [Heq HQ] ].
            inversion Heq; subst. assumption.
      - (* Find contradictory assumption *)
         apply H2 in H5. apply H5 in Pre.
         destruct Pre as [st' [C _] ].
         inversion C.
    Qed.
    
    (** Here are the other proof rules (sanity check) *)
    Theorem hoare_skip : forall P,
         {{P}} skip {{P}}.
    Proof.
      intros P st st' H HP. inversion H. subst.
      eexists. split.
      - reflexivity.
      - assumption.
    Qed.
    
    Theorem hoare_if : forall P Q (b:bexp) c1 c2,
      {{ P /\ b}} c1 {{Q}} ->
      {{ P /\ ~ b}} c2 {{Q}} ->
      {{P}} if b then c1 else c2 end {{Q}}.
    Proof.
      intros P Q b c1 c2 HTrue HFalse st st' HE HP.
      inversion HE; subst.
      - (* b is true *)
        apply (HTrue st st').
        + assumption.
        + split; assumption. 
      - (* b is false *)
        apply (HFalse st st').
        + assumption.
        + split.
          * assumption.
          * apply bexp_eval_false. assumption.
    Qed.
    
    Theorem hoare_while : forall P (b:bexp) c,
      {{P /\ b}} c {{P}} ->
      {{P}} while b do c end {{ P /\ ~b}}.
    Proof.
      intros P b c Hhoare st st' He HP.
      remember <{while b do c end}> as wcom eqn:Heqwcom.
      induction He;
        try (inversion Heqwcom); subst; clear Heqwcom.
      - (* E_WhileFalse *)
        eexists. split.
        + reflexivity.
        + split; try assumption.
          apply bexp_eval_false. assumption.
      - (* E_WhileTrueNormal *)
        clear IHHe1.
        apply IHHe2.
        + reflexivity.
        + clear IHHe2 He2 r.
          unfold hoare_triple in Hhoare.
          apply Hhoare in He1.
          * destruct He1 as [st1 [Heq Hst1] ].
            inversion Heq; subst.
            assumption.
          * split; assumption.
      - (* E_WhileTrueError *)
         exfalso. clear IHHe.
         unfold hoare_triple in Hhoare.
         apply Hhoare in He.
         + destruct He as [st' [C _] ]. inversion C.
         + split; assumption.
    Qed.
    
    (** Finally, state Hoare rules for [assert] and [assume] and use them
        to prove a simple program correct.  Name your rules [hoare_assert]
        and [hoare_assume]. *)
    
    (* FILL IN HERE *)
    
    (** Use your rules to prove the following triple. *)
    
    Example assert_assume_example:
      {{True}}
        assume (X = 1);
        X := X + 1;
        assert (X = 2)
      {{True}}.
    Proof.
    (* FILL IN HERE *) Admitted.
    
    End HoareAssertAssume.
    (** [] *)
    
