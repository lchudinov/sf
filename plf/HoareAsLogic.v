Set Warnings "-deprecated-hint-without-locality,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From PLF Require Import Hoare.
Hint Constructors ceval : core.

Definition valid (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
    st =[ c ]=> st' ->
    P st ->
    Q st'.

Inductive derivable : Assertion -> com -> Assertion -> Type :=
  | H_Skip : forall P,
      derivable P <{skip}> P
  | H_Asgn : forall Q V a,
      derivable (Q [V |-> a]) <{V := a}> Q
  | H_Seq : forall P c Q d R,
      derivable Q d R -> derivable P c Q -> derivable P <{c;d}> R
  | H_If : forall P Q b c1 c2,
    derivable (fun st => P st /\ bassn b st) c1 Q ->
    derivable (fun st => P st /\ ~(bassn b st)) c2 Q ->
    derivable P <{if b then c1 else c2 end}> Q
  | H_While : forall P b c,
    derivable (fun st => P st /\ bassn b st) c P ->
    derivable P <{while b do c end}> (fun st => P st /\ ~ (bassn b st))
  | H_Consequence : forall (P Q P' Q' : Assertion) c,
    derivable P' c Q' ->
    (forall st, P st -> P' st) ->
    (forall st, Q' st -> Q st) ->
    derivable P c Q.

Lemma H_Consequence_pre : forall (P Q P': Assertion) c,
    derivable P' c Q ->
    (forall st, P st -> P' st) ->
    derivable P c Q.
Proof. eauto using H_Consequence. Qed.

Lemma H_Consequence_post : forall (P Q Q' : Assertion) c,
    derivable P c Q' ->
    (forall st, Q' st -> Q st) ->
    derivable P c Q.
Proof. eauto using H_Consequence. Qed.

(*
  {{(X=3) [X |-> X + 2] [X |-> X + 1]}}
    X := X + 1;
    X := X + 2
  {{X=3}}
*)
Example sample_proof :
derivable
((fun st:state => st X = 3) [X |-> X + 2] [X |-> X + 1])
<{ X := X + 1; X := X + 2}>
(fun st:state => st X = 3).
Proof.
eapply H_Seq.
- apply H_Asgn.
- apply H_Asgn.
Qed.

Theorem provable_true_post : forall c P,
    derivable P c True.
Proof.
  intros.
  induction c.
  Admitted.

