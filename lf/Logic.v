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
  
  