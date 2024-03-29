From LF Require Export Tactics.

Check (3 = 3) : Prop.
Check (forall n m : nat, n + m = m + n) : Prop.
Check 2 = 2 : Prop.
Check 3 = 2 : Prop.
Check forall n : nat, n = 2 : Prop.

Theorem plus_2_2_is_4 :
  2 + 2 = 4.
Proof. reflexivity. Qed.

Definition plus_claim : Prop := 2 + 2 = 4.
Check plus_claim : Prop.

Theorem plus_claim_is_true :
  plus_claim.
Proof. reflexivity. Qed.

Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three : nat -> Prop.

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.
Lemma succ_inj : injective S.
Proof.
  intros n m H. injection H as H1. apply H1.
Qed.
Check @eq : forall A : Type, A -> A -> Prop.

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - reflexivity.
  - reflexivity.
Qed.

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m H.
  split.
  - induction n as [|n'].
    + reflexivity.
    + rewrite add_comm in H. rewrite <- plus_n_Sm in H. discriminate H.
  - induction m.
    + reflexivity.
    + rewrite <- plus_n_Sm in H. discriminate H.
Qed.

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example2'' :
  forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros n m Hn Hm.
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n m H.
  apply and_exercise in H.
  destruct H as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q HPQ.
  destruct HPQ as [HP _].
  apply HP. Qed.

  Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q HPQ.
  destruct HPQ as [_ HQ].
  apply HQ.
Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
    - (* left *) apply HQ.
    - (* right *) apply HP.
Qed.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  - split.
    + apply HP.
    + apply HQ.
  - apply HR.
Qed.

Check @and : Prop -> Prop -> Prop.

Lemma factor_is_O:
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  (* This pattern implicitly does case analysis on
     n = 0 ∨ m = 0 *)
  intros n m [Hn | Hm].
  - (* Here, n = 0 *)
    rewrite Hn. reflexivity.
  - (* Here, m = 0 *)
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.

Lemma or_intro_l : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  (* WORKED IN CLASS *)
  intros [|n'].
  - left. reflexivity.
  - right. reflexivity.
Qed.

Lemma mult_is_O :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H.
  destruct n as [|n'].
  - left. reflexivity.
  - right. destruct m as [|m'].
    + reflexivity.
    + discriminate.
Qed.

Theorem or_commut : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros P Q [PH | QH].
  - right. apply PH.
  - left. apply QH.
Qed.
  
Module NotPlayground.
Definition not (P:Prop) := P -> False.
Notation "~ x" := (not x) : type_scope.
Check not : Prop -> Prop.
End NotPlayground.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  destruct contra. Qed.

  Theorem not_implies_our_not : forall (P : Prop),
  ~ P -> (forall (Q : Prop), P -> Q).
Proof.
  intros P HNP Q contra.
  unfold not in HNP. apply HNP in contra. destruct contra.
Qed.

Theorem zero_not_one : 0 <> 1.
Proof.
  unfold not.
  intros contra.
  discriminate contra.
Qed.

Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. destruct H.
Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ not P) -> Q.
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HP HNA]. unfold not in HNA.
  apply HNA in HP. destruct HP.
Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not. intros G. apply G. apply H.
 Qed.

 Theorem contrapositive : forall (P Q : Prop),
 (P -> Q) -> (~ Q -> ~P).
Proof.
 intros P Q HPQ.
 unfold not.
 intros QFH PH.
 apply QFH in HPQ. destruct HPQ.
 - apply PH.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intros P [HA HB].
  unfold not in HB.
  apply HB in HA.
  destruct HA.
Qed.

Theorem de_morgan_not_or : forall (P Q : Prop),
    not (P \/ Q) -> not P /\ not Q.
Proof.
  intros P Q H.
  unfold not in H.
  split.
  - intros HP. apply or_intro_l  with (B:=Q) in HP. apply H. apply HP.
  - intros HQ. apply or_intro_l with (B:=P) in HQ. apply or_commut in HQ. apply H. apply HQ.
Qed.

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros b H.
  destruct b eqn:HE.
  - (* b = true *)
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
Qed.

Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - unfold not in H.
    exfalso.
    apply H. reflexivity.
  - reflexivity.
Qed.

Lemma True_is_true : True.
Proof. apply I. Qed.

Definition disc_fn (n: nat) : Prop :=
  match n with
  | O => True
  | S _ => False
end.

Theorem disc_example : forall n, not (O = S n).
Proof.
  intros n H1.
  assert (H2 : disc_fn O). { simpl. apply I. }
  rewrite H1 in H2. simpl in H2. apply H2.
Qed.

Module IffPlayground.
Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).
Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.
End IffPlayground.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HAB HBA].
  split.
  - (* -> *) apply HBA.
  - (* <- *) apply HAB.
Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  (* WORKED IN CLASS *)
  intros b. split.
  - (* -> *) apply not_true_is_false.
  - (* <- *)
    intros H. rewrite H. intros H'. discriminate H'.
Qed.

Lemma apply_iff_example1:
  forall P Q R : Prop, (P <-> Q) -> (Q -> R) -> (P -> R).
Proof.
  intros P Q R Hiff H HP. apply H. apply Hiff. apply HP.
Qed.
Lemma apply_iff_example2:
  forall P Q R : Prop, (P <-> Q) -> (P -> R) -> (Q -> R).
Proof.
  intros P Q R Hiff H HQ. apply H. apply Hiff. apply HQ.
Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  - intros [HP | [HQ HR]].
    + split.
      * left. apply HP.
      * left. apply HP.
    + split. 
      * right. apply HQ.
      * right. apply HR.
  - intros [[HP1 | HQ] [HP2 | HR]].
    + left. apply HP1.
    + left. apply HP1.
    + left. apply HP2.
    + right. split.
      * apply HQ.
      * apply HR.
Qed.

From Coq Require Import Setoids.Setoid.

Lemma mul_eq_0 : forall n m,
  n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_is_O.
  - apply factor_is_O.
Qed.

Theorem  or_assoc: forall P Q R : Prop,
  P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R.
  split.
  - intros [HP | [HQ | HR]].
    + left. left. apply HP.
    + left. right. apply HQ.
    + right. apply HR.
  - intros [[HP | HQ] | HR].
    + left. apply HP.
    + right. left. apply HQ.
    + right. right. apply HR.
Qed.

Lemma mul_eq_0_ternary : forall n m p,
  n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mul_eq_0.
  rewrite mul_eq_0.
  rewrite or_assoc.
  reflexivity.
Qed.

Definition Even x := exists n : nat, x = double n.

Lemma four_is_Even : Even 4.
Proof.
  unfold Even. exists 2. reflexivity.
Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) -> (exists o, n = 2 + o).
Proof.
  intros n [m Hm].
  exists (2 + m).
  apply Hm.
Qed.

Theorem dist_not_exists : forall (X : Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P.
  unfold not.
  intros H [x Hx].
  apply Hx.
  apply H.
Qed.

Theorem dist_exists_or : forall (X : Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q.
  split.
  - intros [x [HP | HQ]].
    + left. exists x. apply HP.
    + right. exists x. apply HQ.
  - intros [[x HP] | [x HQ]].
    + exists x. left. apply HP.
    + exists x. right. apply HQ.
Qed.

Theorem leb_plus_exists : forall n m,
  n <=? m = true -> exists x, m = n + x.
Proof.
  induction n.
  - intros m H. exists m. reflexivity.
  - destruct m.
    + simpl. discriminate.
    + simpl.
      intros H.
      apply IHn in H.
      destruct H as [x0 H1].
      exists x0.
      rewrite H1.
      reflexivity.
Qed.
  
Theorem plus_exists_leb : forall n m,
  (exists x, m = n + x) -> n <=? m = true.
Proof.
  intros n m H.
  destruct H as [x0 H].
  generalize dependent m.
  induction n as [|n' IHn'].
  - reflexivity.
  - intros m H.
    destruct m as [|m'] eqn:Em.
    + discriminate H.
    + rewrite add_comm in H.
      rewrite <- plus_n_Sm in H.
      injection H as H.
      rewrite add_comm in H.
      apply IHn' in H.
      simpl.
      apply H.
Qed.

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2 : forall n,
  In n [2; 4] -> exists n', n = 2 * n'.
Proof.
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.

Theorem In_map : forall (A B : Type) (f : A -> B) (l : list A) (x : A),
         In x l -> In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - simpl. intros [].
  - simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

Theorem In_map_iff : forall (A B : Type) (f : A -> B) (l : list A) (y : B),
  In y (map f l) <-> exists x, f x = y /\ In x l.
Proof.
  intros A B f l y. split.
  - induction l as [|x' l' IHl'].
    + intros H. simpl in H. exfalso. apply H.
    + simpl. intros [H1 | H2].
      * exists x'. split.
        -- apply H1.
        -- left. reflexivity.
      * apply IHl' in H2.
        destruct H2 as [x0 [H2 H3]].
        exists x0. split.
        -- apply H2.
        -- right. apply H3.
  - intros [x0 [H1 H2]].
    rewrite <- H1.
    apply In_map. apply H2.
Qed.

Theorem In_app_iff : forall A l l' (a : A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l. induction l as [|a' l' IH].
  - simpl. 
    split.
    + intros H. right. apply H.
    + intros [H1 | H2].
      * exfalso. apply H1.
      * apply H2.
  - split.
    + simpl.
      intros [H1 | H2].
      * left. left. apply H1.
      * rewrite <- or_assoc. right. apply IH. apply H2.
    + intros [H1 | H2].
      * simpl. simpl in H1. destruct H1 as [H1 | H1].
        -- left. apply H1.
        -- right. apply IH. left. apply H1.
      * simpl. right. apply IH. right. apply H2.
Qed.

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | h :: t => P h /\ All P t
  end.

Theorem All_In : forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <-> All P l.
Proof.
  intros T P l. split.
  - induction l as [|h t IHt].
    + simpl. intros H. apply I.
    + simpl. intros H. split.
      * apply H. left. reflexivity.
      * apply IHt. intros x. intros H1. apply H. right. apply H1.
  - induction l as [|h t IHt].
    + simpl. intros H M. apply ex_falso_quodlibet.
    + simpl. intros [H1 H2]. intros x. intros [H3 | H4].
      * rewrite <- H3. apply H1.
      * apply IHt. apply H2. apply H4.
Qed.

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  fun n => if odd n then Podd n else Peven n. 

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (odd n = true -> Podd n) ->
    (odd n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros Podd Peven n.
  intros H1 H2.
  unfold combine_odd_even.
  destruct (odd n) as [] eqn:E.
  - apply H1. reflexivity.
  - apply H2. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd : forall (Podd Peven : nat -> Prop) (n : nat),
  combine_odd_even Podd Peven n -> odd n = true -> Podd n.
Proof.
  intros Podd Peven n.
  unfold combine_odd_even.
  destruct (odd n) as [] eqn:E.
  - intros. apply H.
  - intros. discriminate H0.
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = false ->
    Peven n.
Proof.
  intros Podd Peven n.
  unfold combine_odd_even.
  destruct (odd n) as [] eqn:E.
  - intros. discriminate H0.
  - intros. apply H.
Qed.

Check plus : nat -> nat -> nat.
Check add_comm : forall n m : nat, n + m = m + n.

Lemma add_comm3 : forall x y z,
  x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite add_comm.
  rewrite add_comm.
Abort.

Lemma add_comm3_take2 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite add_comm.
  assert (H : y + z = z + y).
    { rewrite add_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

Lemma add_comm3_take3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite add_comm.
  rewrite (add_comm y z).
  reflexivity.
Qed.

Theorem in_not_nil :
  forall A (x : A) (l : list A), In x l -> l <> [].
Proof.
  intros A x l H.
  unfold not. intros Hl.
  rewrite Hl in H. simpl in H.
  apply H.
Qed.

Lemma in_not_nil_42 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  Fail apply in_not_nil.
Abort.

Lemma in_not_nil_42_take2 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil with (x := 42).
  apply H.
Qed.

Lemma in_not_nil_42_take3 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil in H.
  apply H.
Qed.

Lemma in_not_nil_42_take4 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil nat 42).
  apply H.
Qed.

Lemma in_not_nil_42_take5 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil _ _ _ H).
Qed.

Example lemma_application_ex : forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) -> n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
           as [m [Hm _]].
  rewrite mul_0_r in Hm. rewrite <- Hm. reflexivity.
Qed.

Example function_equality_ex_1 : 
  (fun x => 3 + x) = (fun x => (pred 4) + x).
Proof. reflexivity. Qed.

Example function_equality_ex_2_stuck :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof. (* Stuck *) Abort.

Axiom functional_extensionality : forall {X Y : Type} {f g : X -> Y},
  (forall (x : X), f x = g x) -> f = g.

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality.
  intros x.
  apply add_comm.
Qed.

Print Assumptions function_equality_ex2.
  
Fixpoint rev_append {X} (l_1 l_2 : list X) : list X :=
  match l_1 with
  | [] => l_2
  | x :: l_1' => rev_append l_1' (x :: l_2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

Lemma rev_append_nil : forall X (l1 l2 : list X), rev_append l1 l2 = rev_append l1 [] ++ l2.
Proof.
  intros X l1 l2.
  generalize dependent l2.
  induction l1.
  - reflexivity.
  - intros l2.
    simpl.
    rewrite -> IHl1. rewrite -> (IHl1 [x]). rewrite -> app_assoc. reflexivity.
  Qed.
  
Theorem tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
  intros X.
  apply functional_extensionality.
  unfold tr_rev.
  induction x as [|h t IHx].
  - reflexivity.
  - simpl. rewrite <- IHx.
    apply rev_append_nil.
Qed.
Example even_42_bool : even 42 = true.
Proof. reflexivity. Qed.

Example even_42_prop : Even 42.
Proof. unfold Even. exists 21. reflexivity. Qed.

Lemma even_double : forall k, even (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed
.
Lemma even_double_conv : forall n, exists k,
  n = if even n then double k else S (double k).
Proof.
  intros n. induction n as [|n' IHn'].
  - simpl. exists 0. simpl. reflexivity.
  - rewrite even_S.
    destruct (even n') eqn:E.
    + simpl. destruct IHn' as [k']. exists k'. rewrite H. reflexivity.
    + simpl. destruct IHn' as [k']. exists (S k'). rewrite H. reflexivity.
Qed.

Theorem even_bool_prop : forall n,
  even n = true <-> Even n.
Proof.
  intros n. split.
  - intros H. destruct (even_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. unfold Even. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply even_double.
Qed.

Theorem eqb_eq : forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply eqb_true.
  - intros H. rewrite H. rewrite eqb_refl. reflexivity.
Qed.

Example even_1000 : Even 1000.
Proof. unfold Even. exists 500. reflexivity. Qed.

Example even_1000' : even 1000 = true.
Proof. reflexivity. Qed.

Example even_1000'' : Even 1000.
Proof. apply even_bool_prop. reflexivity. Qed.

Example not_even_1001 : even 1001 = false.
Proof.
  (* WORKED IN CLASS *)
  reflexivity.
Qed.

Example not_even_1001' : ~(Even 1001).
Proof.
  (* WORKED IN CLASS *)
  rewrite <- even_bool_prop.
  unfold not.
  simpl.
  intro H.
  discriminate H.
Qed.

Lemma plus_eqb_example : forall n m p : nat,
  n =? m = true -> n + p =? m + p = true.
Proof.
  (* WORKED IN CLASS *)
  intros n m p H.
  rewrite eqb_eq in H.
  rewrite H.
  rewrite eqb_eq.
  reflexivity.
Qed.

Theorem andb_true_iff : forall b1 b2:bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros b1 b2. split.
  - intros. split.
    + destruct b1.
      * reflexivity.
      * discriminate.
    + destruct b2.
      * reflexivity.
      * destruct b1 in H.
        -- discriminate H.
        -- discriminate H.
  - intros [H1 H2].
    rewrite H1. rewrite H2. reflexivity.
Qed.

Theorem orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  intros b1 b2. split.
  - intros H.
    destruct (b1) eqn:E in H.
    + left. apply E.
    + right. simpl in H. apply H.
  - intros [H1 | H2].
    + rewrite H1. simpl. reflexivity.
    + rewrite H2. destruct b1 eqn:E.
      * reflexivity.
      * reflexivity.
Qed.

Theorem eqb_neq : forall x y : nat,
  x =? y = false <-> x <> y.
Proof.
  intros x y.
  rewrite <- not_true_iff_false.
  split.
  - intros H.
    destruct (x =? y) eqn:E.
    + intros H1. unfold not in H. apply H. reflexivity.
    + intros H1. rewrite H1 in E. rewrite eqb_refl in E. discriminate E.
  - unfold not.
    intros H.
    destruct (x =? y) eqn:E.
    + intros H1. apply eqb_true in E. rewrite E in H. apply H. reflexivity.
    + intros H1. discriminate H1.
Qed.

Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool)
  (l1 l2 : list A) : bool := 
  match l1, l2 with
  | [], [] => true
  | h1::t1, [] => false
  | [], h2::t2 => false
  | h1::t1, h2::t2 => eqb h1 h2  && eqb_list eqb t1 t2
  end.

Theorem eqb_list_true_iff : forall A (eqb : A -> A -> bool),
    (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
  intros A eqb H. split.
  - generalize dependent l2.
    induction l1 as [|h1 t1].
    + destruct l2 as [|h2 t2] eqn:L2.
      * simpl. reflexivity.
      * simpl. discriminate.
    + destruct l2 as [|h2 t2] eqn:L2.
      * simpl. discriminate.
      * simpl. intros H2. rewrite andb_true_iff in H2. destruct H2 as [H21 H22].
        rewrite H in H21. apply IHt1 in H22. rewrite H21. rewrite H22. reflexivity.
  - generalize dependent l2.
    induction l1 as [|h1 t1].
    + intros l2 H2. rewrite <- H2. reflexivity.
    + destruct l2 as [|h2 t2] eqn:L2.
      * discriminate.
      * simpl. intros H1. injection H1 as H11 H12.
        rewrite andb_true_iff. split.
        -- rewrite H11. rewrite H. reflexivity.
        -- apply IHt1. rewrite H12. reflexivity.
Qed.

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) :=
  match l with
  | [] => true
  | h :: t => if test h then forallb test t else false
  end.

Theorem forallb_true_iff : forall X test (l : list X),
  forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  intros X test l.
  split.
  - induction l as [|h t].
    + simpl. intros []. apply I.
    + simpl. destruct (test h) eqn:E.
      * intros H. split.
        -- reflexivity.
        -- apply IHt. apply H.
      * discriminate.
  - induction l as [|h t].
    + simpl. reflexivity.
    + simpl. destruct (test h) eqn:E.
      * intros [H1 H2]. apply IHt. apply H2.
      * intros [H1 H2]. discriminate H1.
Qed.

Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ ~ P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. intros contra. discriminate contra.
Qed.

Theorem restricted_excluded_middle_eq : forall (n m : nat),
  n = m \/ n <> m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (n =? m)).
  symmetry.
  apply eqb_eq.
Qed.


Theorem excluded_middle_irrefutable: forall (P : Prop),
  ~ ~ (P \/ ~ P).
Proof.
  intros. unfold not. intros. apply H. right. intros HP. apply H. left. apply HP.
Qed.

Definition excluded_middle := forall P : Prop,
  P \/ not P.

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  unfold excluded_middle.
  intros H1 X P H2 x.
  destruct (H1 (P x)) as [Hx | Hy].
  - apply Hx.
  - exfalso. apply H2. exists x. apply Hy.
Qed.
  

Definition peirce := forall P Q: Prop,
  ((P -> Q) -> P) -> P.
Definition double_negation_elimination := forall P:Prop,
  ~~P -> P.
Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P /\ not Q) -> P \/ Q.
Definition implies_to_or := forall P Q:Prop,
  (P -> Q) -> (not P \/ Q).
  
Theorem peirce_double_negation_elimination :
  peirce -> double_negation_elimination.
Proof.
  unfold peirce. unfold double_negation_elimination. unfold not.
  intros H P H1.
  apply H with (Q:=False).
  intros H2. exfalso. apply H1. apply H2.
Qed.

Theorem de_morgan_not_and_not_implies_to_or :
  de_morgan_not_and_not -> implies_to_or.
Proof.
  unfold de_morgan_not_and_not. unfold implies_to_or.
  intros.
  apply H.
  intros H1. unfold not in H1. destruct H1 as [H11 H12].
  apply H11. intros H2. apply H12. apply H0. apply H2.
Qed.

Theorem implies_to_or_excluded_middle :
  implies_to_or -> excluded_middle.
Proof.
  unfold implies_to_or. unfold excluded_middle.
  intros.
  apply or_commut. apply H. intros HP. apply HP.
Qed.

Theorem  excluded_middle_peirce :
  excluded_middle -> peirce.
Proof.
  unfold excluded_middle. unfold peirce.
  intros.
  destruct (H P) as [H1 | H2].
  - apply H1.
  - apply H0. intros H1. exfalso. apply H2. apply H1.
Qed.

