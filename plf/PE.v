From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.
From PLF Require Import Smallstep.
From PLF Require Import Imp.

Definition pe_state := list (string * nat).

Fixpoint pe_lookup (pe_st : pe_state) (V: string) : option nat :=
  match pe_st with
  | [] => None
  | (V', n') :: pe_st => if String.eqb V V' then Some n' else pe_lookup pe_st V
  end.

Definition empty_pe_state : pe_state := [].

Tactic Notation "compare" ident(i) ident(j) :=
  let H := fresh "Heq" i j in
    destruct (String.eqb_spec i j) as [H|H];
    [subst j |].
    
Theorem pe_domain: forall pe_st V n,
  pe_lookup pe_st V = Some n ->
  In V (map (@fst _ _) pe_st).
Proof. intros pe_st V n H. induction pe_st as [| [V' n'] pe_st].
  - (*  *) inversion H.
  - (* :: *) simpl in H. simpl. compare V V'; auto.
Qed.

Print In.
Check filter_In.

Fixpoint inb {A : Type} (eqb : A -> A -> bool) (a : A) (l : list A) :=
  match l with
  | [] => false
  | a'::l' => eqb a a' || inb eqb a l'
end.

Lemma inbP : forall A : Type, forall eqb : A->A->bool,
  (forall a1 a2, reflect (a1 = a2) (eqb a1 a2)) ->
  forall a l, reflect (In a l) (inb eqb a l).
Proof.
  intros A eqb beqP a l.
  induction l as [|a' l' IH].
  - constructor. intros [].
  - simpl. destruct (beqP a a').
    + subst. constructor. left. reflexivity.
    + simpl. destruct IH; constructor.
      * right. trivial.
      * intros [H1 | H2]; congruence.
Qed.

Print reflect.

Fixpoint pe_aexp (pe_st : pe_state) (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId i => match pe_lookup pe_st i with (* <----- NEW *)
             | Some n => ANum n
             | None => AId i
             end
  | <{ a1 + a2 }> =>
      match (pe_aexp pe_st a1, pe_aexp pe_st a2) with
      | (ANum n1, ANum n2) => ANum (n1 + n2)
      | (a1', a2') => <{ a1' + a2' }>
      end
  | <{ a1 - a2 }> =>
      match (pe_aexp pe_st a1, pe_aexp pe_st a2) with
      | (ANum n1, ANum n2) => ANum (n1 - n2)
      | (a1', a2') => <{ a1' - a2' }>
      end
  | <{ a1 * a2 }> =>
      match (pe_aexp pe_st a1, pe_aexp pe_st a2) with
      | (ANum n1, ANum n2) => ANum (n1 * n2)
      | (a1', a2') => <{ a1' * a2' }>
      end
  end.
  
Example test_pe_aexp1:
  pe_aexp [(X,3)] <{X + 1 + Y}>
  = <{4 + Y}>.
Proof. reflexivity. Qed.

Example text_pe_aexp2:
  pe_aexp [(Y,3)] <{X + 1 + Y}>
  = <{X + 1 + 3}>.
Proof. reflexivity. Qed.

Definition pe_consistent (st:state) (pe_st:pe_state) :=
  forall V n, Some n = pe_lookup pe_st V -> st V = n.
  
Theorem pe_aexp_correct_weak: forall st pe_st, pe_consistent st pe_st ->
  forall a, aeval st a = aeval st (pe_aexp pe_st a).
Proof. unfold pe_consistent. intros st pe_st H a.
  induction a; simpl;
    try reflexivity;
    try (destruct (pe_aexp pe_st a1);
         destruct (pe_aexp pe_st a2);
         rewrite IHa1; rewrite IHa2; reflexivity).
  (* Compared to fold_constants_aexp_sound,
     the only interesting case is AId *)
  - (* AId *)
    remember (pe_lookup pe_st x) as l. destruct l.
    + (* Some *) rewrite H with (n:=n) by apply Heql. reflexivity.
    + (* None *) reflexivity.
Qed.

Fixpoint pe_update (st:state) (pe_st:pe_state) : state :=
  match pe_st with
  | [] => st
  | (V,n)::pe_st => t_update (pe_update st pe_st) V n
  end.

Example test_pe_update:
  pe_update (Y !-> 1) [(X,3);(Z,2)]
  = (X !-> 3 ; Z !-> 2 ; Y !-> 1).
Proof. reflexivity. Qed.

(* A handy consequence of eqb_neq *)
Theorem false_eqb_string : forall x y : string,
   x <> y -> String.eqb x y = false.
Proof.
  intros x y. rewrite String.eqb_neq.
  intros H. apply H.
Qed.

Theorem pe_update_correct: forall st pe_st V0,
  pe_update st pe_st V0 =
  match pe_lookup pe_st V0 with
  | Some n => n
  | None => st V0
  end.
Proof. intros. induction pe_st as [| [V n] pe_st]. reflexivity.
  simpl in *. unfold t_update.
  compare V0 V; auto. rewrite String.eqb_refl; auto. rewrite false_eqb_string; auto.
Qed.

Theorem pe_update_consistent: forall st pe_st,
  pe_consistent (pe_update st pe_st) pe_st.
Proof. intros st pe_st V n H. rewrite pe_update_correct.
  destruct (pe_lookup pe_st V); inversion H. reflexivity. Qed.

Theorem pe_consistent_update: forall st pe_st,
  pe_consistent st pe_st -> forall V, st V = pe_update st pe_st V.
Proof. intros st pe_st H V. rewrite pe_update_correct.
  remember (pe_lookup pe_st V) as l. destruct l; auto. Qed.
  
Theorem pe_aexp_correct: forall (pe_st:pe_state) (a:aexp) (st:state),
  aeval (pe_update st pe_st) a = aeval st (pe_aexp pe_st a).
Proof.
  intros pe_st a st.
  induction a; simpl;
    try reflexivity;
    try (destruct (pe_aexp pe_st a1);
         destruct (pe_aexp pe_st a2);
         rewrite IHa1; rewrite IHa2; reflexivity).
  (* Compared to fold_constants_aexp_sound, the only
     interesting case is AId. *)
  rewrite pe_update_correct. destruct (pe_lookup pe_st x); reflexivity.
Qed.

Fixpoint pe_bexp (pe_st : pe_state) (b : bexp) : bexp :=
  match b with
  | <{ true }> => <{ true }>
  | <{ false }> => <{ false }>
  | <{ a1 = a2 }> =>
      match (pe_aexp pe_st a1, pe_aexp pe_st a2) with
      | (ANum n1, ANum n2) => if n1 =? n2 then <{ true }> else <{ false }>
      | (a1', a2') => <{ a1' = a2' }>
      end
  | <{ a1 <> a2 }> =>
      match (pe_aexp pe_st a1, pe_aexp pe_st a2) with
      | (ANum n1, ANum n2) => if negb (n1 =? n2) then <{ true }> else <{ false }>
      | (a1', a2') => <{ a1' <> a2' }>
      end
  | <{ a1 <= a2 }> =>
      match (pe_aexp pe_st a1, pe_aexp pe_st a2) with
      | (ANum n1, ANum n2) => if n1 <=? n2 then <{ true }> else <{ false }>
      | (a1', a2') => <{ a1' <= a2' }>
      end
  | <{ a1 > a2 }> =>
      match (pe_aexp pe_st a1, pe_aexp pe_st a2) with
      | (ANum n1, ANum n2) => if n1 <=? n2 then <{ false }> else <{ true }>
      | (a1', a2') => <{ a1' > a2' }>
      end
  | <{ ~ b1 }> =>
      match (pe_bexp pe_st b1) with
      | <{ true }> => <{ false }>
      | <{ false }> => <{ true }>
      | b1' => <{ ~ b1' }>
      end
  | <{ b1 && b2 }> =>
      match (pe_bexp pe_st b1, pe_bexp pe_st b2) with
      | (<{ true }>, <{ true }>) => <{ true }>
      | (<{ true }>, <{ false }>) => <{ false }>
      | (<{ false }>, <{ true }>) => <{ false }>
      | (<{ false }>, <{ false }>) => <{ false }>
      | (b1', b2') => <{ b1' && b2' }>
      end
  end.
Example test_pe_bexp1:
  pe_bexp [(X,3)] <{~(X <= 3)}>
  = <{ false }>.
Proof. reflexivity. Qed.

Example test_pe_bexp2: forall b:bexp,
  b = <{ ~(X <= (X + 1)) }> ->
  pe_bexp [] b = b.
Proof. intros b H. rewrite -> H. simpl. reflexivity. Qed.

Theorem pe_bexp_correct: forall (pe_st:pe_state) (b:bexp) (st:state),
  beval (pe_update st pe_st) b = beval st (pe_bexp pe_st b).
Proof.
  intros pe_st b st.
  induction b; simpl;
    try reflexivity;
    try (remember (pe_aexp pe_st a1) as a1';
         remember (pe_aexp pe_st a2) as a2';
         assert (H1: aeval (pe_update st pe_st) a1 = aeval st a1');
         assert (H2: aeval (pe_update st pe_st) a2 = aeval st a2');
           try (subst; apply pe_aexp_correct);
         destruct a1'; destruct a2'; rewrite H1; rewrite H2;
         simpl; try destruct (n =? n0);
         try destruct (n <=? n0); reflexivity);
    try (destruct (pe_bexp pe_st b); rewrite IHb; reflexivity);
    try (destruct (pe_bexp pe_st b1);
         destruct (pe_bexp pe_st b2);
         rewrite IHb1; rewrite IHb2; reflexivity).
Qed.