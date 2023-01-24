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

Theorem minus_n_n: forall n,
  n - n = 0.
Proof.
  intros n. induction n as [| k].
   - reflexivity.
   - simpl. rewrite -> IHk. reflexivity.
Qed.

Theorem plus_n_Sm: forall n m : nat,
  S (n + m) = n + S m.
Proof.
  intros n m. induction n as [| n'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem add_comm : forall a b : nat,
  a + b = b + a.
Proof.
  intros a b. induction a as [| a'].
  - simpl. rewrite add_0_r. reflexivity.
  - simpl. rewrite IHa'. rewrite plus_n_Sm. reflexivity.
Qed.
  