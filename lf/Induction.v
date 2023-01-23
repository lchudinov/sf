From LF Require Export Basics. 

Example add_0_1 : forall n : nat,
  0 + n = n.
Proof. reflexivity. Qed.

Example add_0_r_firsttry : forall n : nat,
  n + 0 = n.
Proof.
  intros n.
  simpl.
Abort.


Example add_0_r_secondtry : forall n : nat,
  n + 0 = n.
Proof.
  intros n. destruct n as [|n'] eqn:E.
  - reflexivity.
  - simpl.
Abort.

Theorem add_0_r : forall n : nat,
  n + 0 = n.
Proof.
  intros n. induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.