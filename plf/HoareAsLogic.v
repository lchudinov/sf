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
  intros c.
  induction c; intros P.
  - eapply H_Consequence_pre.
    + apply H_Skip.
    + intros. apply I.
  - eapply H_Consequence_pre.
    + apply H_Asgn.
    + intros. apply I.
  - eapply H_Consequence_pre.
    + eapply H_Seq.
      * apply IHc2.
      * apply (IHc1 (fun _ => True)).
    + intros. apply I.
  - eapply H_Consequence_pre.
    + apply H_If.
      * apply IHc1.
      * apply IHc2.
    + intros. apply H.
  - eapply H_Consequence.
    + apply H_While.
      * apply IHc.
    + intros. apply I.
    + intros. apply I.
Qed.
      
Theorem provable_false_pre : forall c Q,
  derivable False c Q.
Proof.
  intro c.
  induction c; intro Q.
  - eapply H_Consequence_pre.
    + apply H_Skip.
    + intros. destruct H.
  - eapply H_Consequence_pre.
    + apply H_Asgn.
    + intros. destruct H.
  - eapply H_Consequence_pre.
    + eapply H_Seq.
      * apply IHc2.
      * apply IHc1.
    + intros. destruct H.
  - eapply H_Consequence_pre.
    + apply H_If.
      * eapply H_Consequence_pre.
        ** apply IHc1.
        ** intro. intros [P Q']. (*** ????????????? *)
  Admitted.

Theorem hoare_sound : forall P c Q,
  derivable P c Q -> valid P c Q.
Proof.
  intros. unfold valid.
  intros.
  Admitted.
  
Definition wp (c:com) (Q:Assertion) : Assertion :=
  fun s => forall s', s =[ c ]=> s' -> Q s'.
  
Hint Unfold wp : core.

Theorem wp_is_precondition : forall c Q,
  {{wp c Q}} c {{Q}}.
Proof. auto. Qed.

Theorem wp_is_weakest : forall c Q P',
    {{P'}} c {{Q}} ->
    P' ->> (wp c Q).
Proof. eauto. Qed.

Lemma wp_seq : forall P Q c1 c2,
  derivable P c1 (wp c2 Q) -> derivable (wp c2 Q) c2 Q -> derivable P <{c1; c2}> Q.
Proof.
  Admitted.

Lemma wp_invariant : forall b c Q,
    valid (wp <{while b do c end}> Q /\ b) c (wp <{while b do c end}> Q).
Proof.
  (* FILL IN HERE *) Admitted.

Theorem hoare_complete: forall P c Q,
  valid P c Q -> derivable P c Q.
Proof.
  unfold valid. intros P c. generalize dependent P.
  induction c; intros P Q HT.
  (* FILL IN HERE *) Admitted.


