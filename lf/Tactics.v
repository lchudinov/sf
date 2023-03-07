From LF Require Export Poly.

Theorem silly1: forall (n m : nat),
  n = m -> n = m.
Proof.
  intros n m eq.
  (* rewrite -> eq. reflexivity. *)
  apply eq.
Qed.

Theorem silly2: forall (n m o p : nat),
  n = m -> (n = m -> [n;o] = [m;p]) -> [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1.
Qed.

Theorem silly2a: forall (n m : nat),
  (n,n) = (m,m) -> (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) -> [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1.
Qed.

Theorem silly_ex : forall p,
  (forall n, even n = true -> even (S n) = false) ->
  (forall n, even n = false -> odd n = true) ->
  even p = true ->
  odd (S p) = true.
Proof.
  intros p eq1 eq2 eq3.
  apply eq2.
  apply eq1.
  apply eq3.
Qed.

Theorem silly3 : forall (n m : nat),
  n = m -> m = n.
Proof.
  intros n m H.
  Fail apply H.
  symmetry. apply H.
Qed.

Search rev.

Theorem rev_exercise1 : forall (l l' : list nat),
  l = rev l' -> l' = rev l.
Proof.
  intros l l' H.
  rewrite H. symmetry. apply rev_involutive.
Qed.
Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity.
Qed.

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2.
  rewrite -> eq1. rewrite -> eq2.
  reflexivity.
Qed.
Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m := [c;d]).
  apply eq1. apply eq2.
Qed.

Example trans_eq_example'' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  transitivity [c;d].
  apply eq1.
  apply eq2.
Qed.

Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros n m o p eq1 eq2.
  transitivity (n+p).
  symmetry. reflexivity.
  transitivity m.
  apply eq2. apply eq1.
Qed.
  
Example trans_eq_exercise' : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros n m o p eq1 eq2.
  transitivity m.
  apply eq2. apply eq1.
Qed.
Theorem S_injective : forall (n m : nat),
  S n = S m -> n = m.
Proof.
  intros n m H1.
  assert (H2: n = pred (S n)). { reflexivity. }
  rewrite H2. rewrite H1. simpl. reflexivity.
Qed.

Theorem S_injective' : forall (n m : nat),
  S n = S m -> n = m.
Proof.
  intros n m H.
  injection H as Hmn. apply Hmn.
Qed.

Theorem injection_ex1 : forall (n m o : nat),
  [n;m] = [o;o] -> n = m.
Proof.
  intros n m o H.
  (* WORKED IN CLASS *)
  injection H as H1 H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.

Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  j = z :: l ->
  x = y.
Proof.
  intros X x y z l j H1.
  injection H1 as H11 H12.
  rewrite <- H12.
  intros H2.
  injection H2 as H21.
  rewrite -> H11.
  rewrite -> H21.
  reflexivity.
Qed.
Theorem discriminate_ex1 : forall (n m : nat),
  false = true -> n = m.
Proof.
  intros n m contra. discriminate contra.
Qed.
  
Theorem discriminate_ex2 : forall (n : nat),
  S n = O -> 2 + 2 = 5.
Proof.
  intros n contra. discriminate contra.
Qed.

Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] -> x = z.
Proof.
  intros X x y z l j contra. discriminate contra.
Qed.
Theorem eqb_0_l : forall n, 0 =? n = true -> n = 0.
Proof.
  intros n.
  destruct n as [|n'] eqn:E.
  - intros H. reflexivity.
  - simpl. intros H. discriminate H.
Qed.

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq. reflexivity. Qed.

Theorem eq_implies_succ_equal : forall (n m : nat),
  n = m -> S n = S m.
Proof. intros n m H. apply f_equal. apply H. Qed.

Theorem eq_implies_succ_equal' : forall (n m : nat),
  n = m -> S n = S m.
Proof. intros n m H. f_equal. apply H. Qed.

Theorem S_inj : forall (n m : nat) (b : bool),
  ((S n) =? (S m)) = b -> (n =? m) = b.
Proof. intros n m b H. simpl in H. apply H. Qed.

Theorem silly4 : forall (n m p q : nat),
  (n = m -> p = q) ->
  m = n ->
  q = p.
Proof.
  intros n m p q EQ H.
  symmetry in H. apply EQ in H. symmetry in H. apply H. Qed.

Theorem double_injective_FAILED : forall n m,
  double n = double m -> n = m.
Proof.
  intros n m. induction n as [| n' IHn'].
  - (* n = O *) simpl. intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *) intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) discriminate eq.
    + (* m = S m' *) apply f_equal.
Abort.
  
Theorem double_injective : forall n m,
  double n = double m -> n = m.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = O *) simpl. intros m eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *) intros m eq. destruct m as [|m'] eqn:E.
    + discriminate eq.
    + apply f_equal. apply IHn'. injection eq as goal. apply goal.
Qed.

Theorem eqb_true : forall n m, n =? m = true -> n = m.
Proof.
  intros n. induction n as [|n' IHn'].
  - intros m eq. destruct m as [|m'] eqn:E.
    + reflexivity.
    + discriminate eq.
  - intros m eq. destruct m as [|m'] eqn:E.
    + discriminate eq.
    + apply f_equal. apply IHn'. simpl in eq. apply eq.
Qed.

Theorem plus_n_n_injective : forall n m,
  n + n = m + m -> n = m.
Proof.
  intros n. induction n as [|n' IHn'].
  - simpl. intros m eq. destruct m as [|m'] eqn:E.
    + reflexivity.
    + rewrite <- plus_n_Sm in eq. discriminate eq.
  - simpl. intros m eq. destruct m as [|m'] eqn:E.
    + simpl in eq. discriminate eq.
    + simpl in eq.
      apply f_equal.
      rewrite <- plus_n_Sm in eq.
      rewrite <- plus_n_Sm in eq.
      injection eq as goal.
      apply IHn' in goal.
      apply goal.
Qed.

Theorem double_injective_take2_FAILED : forall n m,
  double n = double m -> n = m.
Proof.
  intros n m. induction m as [| m' IHm'].
  - (* m = O *) simpl. intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) apply f_equal.
        (* We are stuck here, just like before. *)
Abort.

Theorem double_injective_take2 : forall n m,
  double n = double m -> n = m.
Proof.
  intros n m.
  (* n and m are both in the context *)
  generalize dependent n.
  (* Now n is back in the goal and we can do induction on
     m and get a sufficiently general IH. *)
  induction m as [| m' IHm'].
  - (* m = O *) simpl. intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) apply f_equal.
      apply IHm'. injection eq as goal. apply goal. Qed.

Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
  length l = n -> nth_error l n = None.
Proof.
  intros n X l.
  generalize dependent l.
  induction n as [|n' IHn'].
  - intros l H. destruct l as [|h t].
    + simpl. reflexivity.
    + simpl in H. discriminate H.
  - intros l H. destruct l as [|h t].
    + simpl in H. discriminate H.
    + simpl in H. simpl. injection H. apply IHn'.
Qed.

Theorem nth_error_after_last': forall (n : nat) (X : Type) (l : list X),
  length l = n -> nth_error l n = None.
Proof.
  intros n X l.
  generalize dependent n.
  induction l as [|h t].
  - simpl. reflexivity.
  - destruct n as [|n'].
    + simpl. intros contra. discriminate contra.
    + intros eq. injection eq as eq1. simpl. apply IHt. apply eq1.
Qed.

Definition square n := n * n.

Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  simpl.
  unfold square.
  rewrite mult_assoc.
  assert (H : n * m * n = n * n * m).
    { rewrite mul_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc. reflexivity.
Qed.

Definition foo (x: nat) := 5.

Fact silly_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  simpl.
  reflexivity.
Qed.

Definition bar x :=
  match x with
  | O => 5
  | S _ =>  5
  end.
Fact silly_fact_2_FAILED : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  simpl. (* Does nothing! *)
Abort.

Fact silly_fact_2 : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m. destruct m as [|m'].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Fact silly_fact_2' : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.
  destruct m eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

Definition sillyfun (n : nat) : bool  := 
  if n =? 3 then false
  else if n =? 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat), sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (n =? 3) eqn:E1.
  - reflexivity.
  - destruct (n =? 5) eqn:E2.
    + reflexivity.
    + reflexivity.
Qed.

Theorem split_tail: forall X Y (l : list (X * Y)) (a : X) (b : Y),
  split ((a, b) :: l) = (a :: fst (split l), b :: snd (split l)).
Proof.
  intros X Y l a b.
  simpl.
  destruct (split l) eqn:split.
  simpl.
  reflexivity.
Qed.

Theorem combine_tail: forall X Y (l1: list X) (l2: list Y) (a : X) (b : Y),
  combine (a::l1) (b::l2) = (a, b) :: combine l1 l2.
Proof.
  intros X Y l1 l2 a b.
  simpl.
  destruct (combine l1 l2) eqn:combine.
  - reflexivity.
  - reflexivity.
Qed.



Theorem combine_split_first_attempt: forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) -> combine l1 l2 = l.
Proof.
  Admitted.

Definition sillyfun1 (n : nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
  else false.

Theorem sillyfun1_odd_FAILED : forall (n : nat),
  sillyfun1 n = true -> odd n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3).
  (* stuck... *)
Abort.

Theorem sillyfun1_odd : forall (n : nat),
  sillyfun1 n = true -> odd n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3) eqn:Heqe3.
  - apply eqb_true in Heqe3. rewrite Heqe3. reflexivity.
  - destruct (n =? 5) eqn:Heqe5.
    + apply eqb_true in Heqe5. rewrite Heqe5. reflexivity.
    + discriminate eq.
Qed.

Theorem bool_fn_applied_thrice : forall (f : bool -> bool) (b : bool), 
  f (f (f b)) = f b.
Proof.
  intros f b.
  destruct b.
  - destruct (f true) eqn:A.
    + rewrite A. rewrite A. reflexivity.
    + destruct (f false) eqn:B.
      * rewrite A. reflexivity.
      * rewrite B. reflexivity.
  - destruct (f false) eqn:A.
    + destruct (f true) eqn:B.
      * rewrite B. reflexivity.
      * rewrite A. reflexivity.
    + rewrite A. rewrite A. reflexivity.
Qed.

Theorem eqb_sym : forall (n m : nat),
  (n =? m) = (m =? n).
Proof.
  intros n m.
  destruct (n =? m) eqn:E.
  - symmetry. apply eqb_true in E. rewrite E. apply eqb_refl.
  - generalize dependent m.
    induction n as [|n'].
    + destruct m.
      * intros E. simpl in E. discriminate E.
      * simpl. reflexivity.
    + destruct m.
      * simpl. reflexivity.
      * intros E. simpl in E. apply IHn' in E. simpl. rewrite <- E. reflexivity.
Qed.

Theorem eqb_trans : forall n m p,
  n =? m = true -> m =? p = true -> n =? p = true.
Proof.
  intros n m p.
  intros eq1 eq2.
  apply eqb_true in eq1. apply eqb_true in eq2.
  rewrite eq1. rewrite eq2. apply eqb_refl.
Qed.

Theorem combine_split: forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) -> combine l1 l2 = l.
Proof.
  intros X Y l.
  induction l as [|h t].
  - intros l1 l2 H.
    simpl in H. injection H as eq1 eq2. rewrite <- eq1. rewrite <- eq2. simpl. reflexivity.
  - destruct h as (x, y).
    destruct l1 as [|x'].
    + intros l2 H. simpl in H. destruct (split t) in H. injection H as H1 H2. discriminate H1.
    + destruct l2 as [|y'].
      * intros H. simpl in H. destruct (split t) in H. discriminate H.
      * intros H. simpl.
        assert (G: split t = (l1, l2)). 
        {
          simpl in H. destruct (split t).
          injection H as H. rewrite -> H0. rewrite -> H2. reflexivity.
        }
        apply IHt in G.
        simpl in H. destruct (split t). injection H as H1 H2 H3. rewrite G. rewrite <- H1. rewrite <- H3. reflexivity.
Qed.

Definition split_combine_statement : Prop :=
  forall X Y (l : list (X * Y)) (l1: list X) (l2: list Y),
  length l1 = length l2 -> split (combine l1 l2) = (l1, l2).
  
Theorem split_combine: split_combine_statement.
Proof.
  intros X Y.
  induction l1 as [|h t].
  - intros l2 H. simpl in H. destruct l2 as [|h2 t2].
    + simpl. reflexivity.
    + simpl. discriminate H.
  - intros l2 H. destruct l2 as [|h2 t2].
    + simpl. simpl in H. discriminate H.
    + injection H as H. apply IHt in H. simpl. rewrite H. reflexivity.
Qed. 

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                                 (x : X) (l lf : list X),
  filter test l = x :: lf ->
  test x = true.
Proof.
  intros X test x l lf.
  destruct l as [| x'].
  + simpl. intros H. discriminate H.
  + induction (x' :: l).
    - simpl. intros H. discriminate H.
    - simpl. destruct (test x0) eqn:T.
      * intros H. injection H as H. rewrite -> H in T. apply T.
      * apply IHl0.
Qed.
  
Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) :=
  match l with
  | [] => true
  | h :: t => if test h then forallb test t else false
  end.
  
Example forallb_1: forallb odd [1;3;5;7;9] = true.
Proof. reflexivity. Qed.
Example forallb_2: forallb negb [false;false] = true.
Proof. reflexivity. Qed.
Example forallb_3: forallb even [0;2;4;5] = false.
Proof. reflexivity. Qed.
Example forallb_4: forallb (eqb 5) [] = true.
Proof. reflexivity. Qed.

Fixpoint existsb {X : Type} (test : X -> bool) (l : list X) :=
  match l with
  | [] => false
  | h :: t => if test h then true else existsb test t
  end.
  
Example existsb_1: existsb (eqb 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.
Example existsb_2: existsb (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.
Example existsb_3: existsb odd [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.
Example existsb_4: existsb even [] = false.
Proof. reflexivity. Qed.

Definition existsb' {X : Type} (test : X -> bool) (l : list X) :=
  negb (forallb (fun x => negb (test x)) l).

  Example existsb'_1: existsb' (eqb 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.
Example existsb'_2: existsb' (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.
Example existsb'_3: existsb' odd [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.
Example existsb'_4: existsb' even [] = false.
Proof. reflexivity. Qed.

Theorem existsb_existsb': forall (X : Type) (test : X -> bool) (l : list X), 
  existsb test l = existsb' test l.
Proof.
  intros X test.
  induction l as [|h t].
  - reflexivity.
  - simpl. unfold existsb'. destruct (test h) eqn:E.
    + simpl. rewrite E. simpl. reflexivity. 
    + simpl. rewrite E. rewrite -> IHt. simpl. reflexivity.
Qed.
  
  
Qed.
