Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export IndProp.

(* Inductive ev : nat → Prop := *)
(* | ev_0 : ev 0 *)
(* | ev_SS (n : nat) (H : ev n) : ev (S (S n)). *)

Check ev_SS
  : forall n, ev n -> ev (S (S n)).
  
Theorem ev_4: ev 4.
Proof.
  apply ev_SS. apply ev_SS. apply ev_0.
Qed.
Print ev_4.

Check (ev_SS 2 (ev_SS 0 ev_0)) : ev 4.

Theorem ev_4': ev 4.
Proof.
  apply (ev_SS 2 (ev_SS 0 ev_0)).
Qed.

Theorem ev_4'' : ev 4.
Proof.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_0.
  Show Proof.
Qed.
Definition ev_4''' : ev 4 :=
  ev_SS 2 (ev_SS 0 ev_0).

  Print ev_4.
  (* ===> ev_4    =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)
  Print ev_4'.
  (* ===> ev_4'   =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)
  Print ev_4''.
  (* ===> ev_4''  =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)
  Print ev_4'''.
  (* ===> ev_4''' =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)

Theorem ev_8 : ev 8.
Proof.
  apply ev_SS. apply ev_SS. apply ev_SS. apply ev_SS. apply ev_0.
Qed.

Definition ev_8' : ev 8 :=
  (ev_SS 6 (ev_SS 4 (ev_SS 2 (ev_SS 0 ev_0)))).

Print ev_8.

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n H. simpl.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.

Definition ev_plus4' : forall n, ev n -> ev (4 + n) :=
  fun (n : nat) => fun (H : ev n) => ev_SS (S (S n)) (ev_SS n H).

Definition ev_plus4'' (n : nat) (H : ev n) : ev (4 + n) :=
  ev_SS (S (S n)) (ev_SS n H).

Check ev_plus4''
  : forall n : nat,
    ev n ->
    ev (4 + n).

Definition ev_plus2 : Prop :=
  forall n, forall (E : ev n), ev (n + 2).

Definition ev_plus2' : Prop :=
  forall n, forall (_ : ev n), ev (n + 2).
  
Definition ev_plus2'' : Prop :=
  forall n, ev n -> ev (n + 2).

Definition add1 : nat -> nat.
intro n.
Show Proof.
apply S.
Show Proof.
apply n.
Defined.

Print add1.
Compute add1 1.

Module Props.
Module And.
Inductive and (P Q : Prop) : Prop :=
  | conj : P -> Q -> and P Q.

Arguments conj [P] [Q].

Notation "P /\ Q" := (and P Q) : type_scope.

Print prod.

Theorem proj1' : forall P Q,
  P /\ Q -> P.
Proof.
  intros P Q HPQ. destruct HPQ as [HP HQ]. apply HP.
  Show Proof.
Qed.
Lemma and_comm : forall P Q : Prop, P /\ Q <-> Q /\ P.
Proof.
  intros P Q. split.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
  - intros [HQ HP]. split.
    + apply HP.
    + apply HQ.
  Show Proof.
Qed.

Definition and_comm'_aux P Q (H : P /\ Q) : Q /\ P :=
  match H with
  | conj HP HQ => conj HQ HP
  end.

Definition and_comm' P Q : P /\ Q <-> Q /\ P :=
  conj (and_comm'_aux P Q) (and_comm'_aux Q P).

Definition conj_fact : ∀ P Q R, P ∧ Q → Q ∧ R → P ∧ R
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
End And.

End Props.