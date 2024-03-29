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
End And.

Definition and_comm'_aux P Q (H : P /\ Q) : Q /\ P :=
  match H with
  | conj HP HQ => conj HQ HP
  end.

Definition and_comm' P Q : P /\ Q <-> Q /\ P :=
  conj (and_comm'_aux P Q) (and_comm'_aux Q P).

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  fun (P Q R: Prop) (PQ: P /\ Q) (QR: Q /\ R) => 
    conj (proj1 P Q PQ) (proj2 Q R QR). 

Module Or.

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q.

Arguments or_introl [P] [Q].
Arguments or_intror [P] [Q].

Notation "P \/ Q" := (or P Q) : type_scope.

Definition inj_l : forall (P Q : Prop), P -> P \/ Q :=
  fun P Q HP => or_introl HP.

Theorem inj_l' : forall (P Q : Prop), P -> P \/ Q.
  Proof.
    intros P Q HP. left. apply HP. Show Proof.
  Qed.

Definition or_elim : forall (P Q R : Prop), (P \/ Q) -> (P -> R) -> (Q -> R) -> R :=
  fun P Q R HPQ HPR HQR =>
    match HPQ with
    | or_introl HP => HPR HP
    | or_intror HQ => HQR HQ
    end.

Theorem or_elim' : forall (P Q R : Prop), (P \/ Q) -> (P -> R) -> (Q -> R) -> R.
    Proof.
  intros P Q R HPQ HPR HQR.
  destruct HPQ as [HP | HQ].
  - apply HPR. apply HP.
  - apply HQR. apply HQ.
  Show Proof.
Qed.

Theorem or_commut'' : forall P Q, P \/ Q -> Q \/ P.
Proof.
  intros P Q HPQ.
  destruct HPQ as [HP | HQ].
  - right. apply HP.
  - left. apply HQ.
  Show Proof.
Qed.

End Or.
Definition or_commut' : forall P Q, P \/ Q -> Q \/ P :=
  fun P Q HPQ => match HPQ with
  | or_introl HP => or_intror HP 
  | or_intror HQ => or_introl HQ 
  end.

Module Ex.

Inductive ex {A : Type} (P : A -> Prop) : Prop :=
  | ex_intro : forall x : A, P x -> ex P.

Notation "'extsts' x, p" :=
  (ex (fun x => p))
    (at level 200, right associativity) : type_scope.
End Ex.

Check ex (fun n => ev n) : Prop.

Definition some_nat_is_even : exists n, ev n :=
  ex_intro ev 4 (ev_SS 2 (ev_SS 0 ev_0)).

Compute (fun n => ev (S n)) 1.
Compute ev_SS 2 (ev_SS 0 ev_0).
Check ex (fun n => ev (S n)).

Definition ex_ev_Sn0 : ex (fun n => ev (S n)) :=
  ex_intro (fun n => ev (S n)) 3 (ev_SS 2 (ev_SS 0 ev_0)).

Definition ex_ev_Sn : ex (fun n => ev (S n)) :=
  ex_intro (fun n => ev (S n)) 1 (ev_SS 0 ev_0).
  
Inductive True : Prop :=
| I : True.

Definition p_implies_true : forall P, P -> True :=
  fun P H => I.

Check p_implies_true.
  
Inductive False : Prop := .

Definition false_implies_zero_eq_one : False -> 0 = 1 :=
  fun contra => match contra with end.

Definition ex_falso_quodlibet' : forall P, False -> P :=
  fun P contra => match contra with end.

Module EqualityPlayground.

Inductive eq {X : Type} : X -> X -> Prop :=
  | eq_refl : forall x, eq x x.

Notation "x == y" :=
  (eq x y)
  (at level 70, no associativity)
  : type_scope.

Lemma four: 2 + 2 == 1 + 3.
  Proof. 
  apply eq_refl.
  Show Proof.
Qed.

Definition four' : 2 + 2 == 1 + 3 :=
  eq_refl 4.

Definition singleton : forall (X : Type) (x : X), [] ++ [x] == x :: [] :=
    fun (X : Type) (x : X) => eq_refl [x].

Definition eq_add : forall (n1 n2 : nat), n1 == n2 -> (S n1) == (S n2) :=
  fun n1 n2 Heq =>
    match Heq with
    | eq_refl n => eq_refl (S n)
    end.

Theorem eq_add' : forall (n1 n2 : nat), n1 == n2 -> (S n1) == (S n2).
    Proof.
  intros n1 n2 Heq.
  Fail rewrite Heq.
  destruct Heq.
  Fail reflexivity.
  apply eq_refl.
    Qed.

Definition eq_cons : forall (X : Type) (h1 h2 : X) (t1 t2 : list X),
  h1 == h2 -> t1 == t2 -> h1 :: t1 == h2 :: t2 :=
  fun x h1 h2 t1 t2 Hheq Hteq => match Hheq, Hteq with
  | eq_refl h, eq_refl t => eq_refl (h :: t)
  end.

Lemma equality__leibniz_equality : forall (X : Type) (x y: X),
  x == y -> forall (P : X -> Prop), P x -> P y.
Proof.
  intros.
  destruct H. apply H0.
  Show Proof.
Qed.
Definition equality__leibniz_equality_term : forall (X : Type) (x y: X),
  x == y -> forall P : (X -> Prop), P x -> P y :=
  fun X x y Hxeqy =>
    match Hxeqy with
    | eq_refl a => fun P H => H
    end.

Lemma leibniz_equality__equality : forall (X : Type) (x y: X),
    (forall P:X -> Prop, P x -> P y) -> x == y.
Proof.
  intros X x y H. apply H. apply eq_refl.
  Show Proof.
Qed.

End EqualityPlayground.

Definition and_assoc : forall P Q R : Prop,
    P /\ (Q /\ R) -> (P /\ Q) /\ R :=
  fun P Q R H =>
    match H with
    | conj HP (conj HQ HR) => conj (conj HP HQ) HR
    end.

Definition or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R) :=
  fun P Q R => 
  conj 
    (fun H => match H with
    | or_introl HP => conj (or_introl HP) (or_introl HP)
    | or_intror (conj HQ HR) => conj (or_intror HQ) (or_intror HR)
    end)
    (fun H => match H with
    | conj HPQ HPR => match HPQ, HPR with
                      | or_introl HP, _ => or_introl HP
                      | _, or_introl HP => or_introl HP
                      | or_intror HQ, or_intror HR => or_intror (conj HQ HR)
                      end
    end
    ).
    
Theorem double_neg : forall P : Prop,
    P -> ~~P.
  Proof.
    (* WORKED IN CLASS *)
    intros P H.
    Show Proof.
    unfold not.
    Show Proof.
    intros G.
    Show Proof.
    apply G.
    Show Proof.
    apply H.
    Show Proof.
   Qed.

Definition double_neg' : forall P : Prop, P -> ~~P :=
  fun P H G => G H.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ not P) -> Q.
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HP HNA]. unfold not in HNA.
  Show Proof.
  apply HNA in HP. destruct HP.
  Show Proof.
Qed.

Definition contradiction_implies_anything' : forall P Q : Prop,
  (P /\ not P) -> Q :=
  fun P Q H => match H with
    | conj HP HNP => match (HNP HP) with end
  end.
  
Theorem de_morgan_not_or : forall (P Q : Prop),
  not (P \/ Q) -> not P /\ not Q.
Proof.
  intros P Q H.
  unfold not in H.
  split.
  - intros HP. apply or_intro_l  with (B:=Q) in HP. apply H. apply HP.
  - intros HQ. apply or_intro_l with (B:=P) in HQ. apply or_commut in HQ. apply H. apply HQ.
Qed.

Definition de_morgan_not_or' : forall P Q : Prop,
  ~ (P \/ Q) -> not P /\ not Q :=
  fun P Q H => 
    conj (fun HP => H (or_introl HP)) (fun HQ => H (or_intror HQ))
.

Definition curry : forall P Q R : Prop,
  ((P /\ Q) -> R) -> (P -> (Q -> R)) :=
  fun P Q R H HP HQ => H (conj HP HQ).

Definition uncurry : forall P Q R : Prop,
  (P -> (Q -> R)) -> ((P /\ Q) -> R) :=
  fun P Q R H HPQ => match HPQ with
                     | conj HP HQ => H HP HQ
                     end.

Definition propositional_extensionality : Prop :=
  forall (P Q : Prop), (P <-> Q) -> P = Q.

Theorem pe_implies_or_eq :
  propositional_extensionality -> forall (P Q : Prop), (P \/ Q) = (Q \/ P).
Proof.
  unfold propositional_extensionality.
  intros. apply H. split.
  - intros H1. apply or_commut. apply H1.
  - intros H1. apply or_commut. apply H1.
Qed.

Lemma pe_implies_true_eq :
  propositional_extensionality -> forall (P : Prop), P -> True = P.
Proof.
  intros. apply H. split.
  - intros. apply H0.
  - intros. apply I.
Qed. 

Definition proof_irrelevance : Prop :=
  forall (P : Prop) (pf1 pf2 : P), pf1 = pf2.

Theorem pe_implies_pi :
  propositional_extensionality -> proof_irrelevance.
Proof.
  unfold propositional_extensionality. unfold proof_irrelevance.
  intros. assert (HP: True = P). { apply (pe_implies_true_eq H). apply pf1. }
  destruct HP. rewrite pf1. rewrite pf2. reflexivity.
Qed.
  
End Props.


  