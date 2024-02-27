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

Fixpoint pe_remove (pe_st:pe_state) (V:string) : pe_state :=
  match pe_st with
  | [] => []
  | (V', n')::pe_st => if String.eqb V V' then pe_remove pe_st V
                      else (V',n') :: pe_remove pe_st V
  end.

Theorem pe_remove_correct: forall pe_st V V0,
  pe_lookup (pe_remove pe_st V) V0
  = if String.eqb V V0 then None else pe_lookup pe_st V0.
Proof. intros pe_st V V0. induction pe_st as [| [V' n'] pe_st].
  - (*  *) destruct (String.eqb V V0); simpl; reflexivity.
  - (* :: *) simpl. compare V V'.
    + (* equal *) rewrite IHpe_st.
      destruct (String.eqb_spec V V0). reflexivity.
      rewrite false_eqb_string; auto.
    + (* not equal *) simpl. compare V0 V'.
      * (* equal *) rewrite false_eqb_string; auto.
      * (* not equal *) rewrite IHpe_st. reflexivity.
Qed.

Definition pe_add (pe_st:pe_state) (V:string) (n:nat) : pe_state :=
  (V,n) :: pe_remove pe_st V.

Theorem pe_add_correct: forall pe_st V n V0,
  pe_lookup (pe_add pe_st V n) V0
  = if String.eqb V V0 then Some n else pe_lookup pe_st V0.
Proof. intros pe_st V n V0. unfold pe_add. simpl.
  compare V V0.
  - (* equal *) rewrite String.eqb_refl; auto.
  - (* not equal *) rewrite pe_remove_correct.
    repeat rewrite false_eqb_string; auto.
Qed.

Theorem pe_update_update_remove: forall st pe_st V n,
  t_update (pe_update st pe_st) V n =
  pe_update (t_update st V n) (pe_remove pe_st V).
Proof. intros st pe_st V n. apply functional_extensionality.
  intros V0. unfold t_update. rewrite !pe_update_correct.
  rewrite pe_remove_correct. destruct (String.eqb V V0); reflexivity.
  Qed.

Theorem pe_update_update_add: forall st pe_st V n,
  t_update (pe_update st pe_st) V n =
  pe_update st (pe_add pe_st V n).
Proof. intros st pe_st V n. apply functional_extensionality. intros V0.
  unfold t_update. rewrite !pe_update_correct. rewrite pe_add_correct.
  destruct (String.eqb V V0); reflexivity. Qed.

Definition pe_disagree_at (pe_st1 pe_st2 : pe_state) (V:string) : bool :=
  match pe_lookup pe_st1 V, pe_lookup pe_st2 V with
  | Some x, Some y => negb (x =? y)
  | None, None => false
  | _, _ => true
end.

Theorem pe_disagree_domain: forall (pe_st1 pe_st2 : pe_state) (V:string),
  true = pe_disagree_at pe_st1 pe_st2 V ->
  In V (map (@fst _ _) pe_st1 ++ map (@fst _ _) pe_st2).
Proof. unfold pe_disagree_at. intros pe_st1 pe_st2 V H.
  apply in_app_iff.
  remember (pe_lookup pe_st1 V) as lookup1.
  destruct lookup1 as [n1|]. left. apply pe_domain with n1. auto.
  remember (pe_lookup pe_st2 V) as lookup2.
  destruct lookup2 as [n2|]. right. apply pe_domain with n2. auto.
  inversion H.
Qed.

Fixpoint pe_unique (l : list string) : list string :=
  match l with
  | [] => []
  | x::l =>
      x :: filter (fun y => if String.eqb x y then false else true) (pe_unique l)
  end.

Theorem pe_unique_correct: forall l x,
  In x l <-> In x (pe_unique l).
Proof. intros l x. induction l as [| h t]. reflexivity.
  simpl in *. split.
  - (* -> *)
    intros. inversion H; clear H.
      left. assumption.
      destruct (String.eqb_spec h x).
         left. assumption.
         right. apply filter_In. split.
           apply IHt. assumption.
           rewrite false_eqb_string; auto.
  - (* <- *)
    intros. inversion H; clear H.
       left. assumption.
       apply filter_In in H0. inversion H0. right. apply IHt. assumption.
Qed.

Definition pe_compare (pe_st1 pe_st2 : pe_state) : list string :=
  pe_unique (filter (pe_disagree_at pe_st1 pe_st2)
    (map (@fst _ _) pe_st1 ++ map (@fst _ _) pe_st2)).

Theorem pe_compare_correct: forall pe_st1 pe_st2 V,
  pe_lookup pe_st1 V = pe_lookup pe_st2 V <->
  ~ In V (pe_compare pe_st1 pe_st2).
Proof. intros pe_st1 pe_st2 V.
  unfold pe_compare. rewrite <- pe_unique_correct. rewrite filter_In.
  split; intros Heq.
  - (* -> *)
    intro. destruct H. unfold pe_disagree_at in H0. rewrite Heq in H0.
    destruct (pe_lookup pe_st2 V).
    rewrite -> eqb_refl in H0. inversion H0.
    inversion H0.
  - (* <- *)
    assert (Hagree: pe_disagree_at pe_st1 pe_st2 V = false).
    { (* Proof of assertion *)
      remember (pe_disagree_at pe_st1 pe_st2 V) as disagree.
      destruct disagree; [| reflexivity].
      apply pe_disagree_domain in Heqdisagree.
      exfalso. apply Heq. split. assumption. reflexivity. }
    unfold pe_disagree_at in Hagree.
    destruct (pe_lookup pe_st1 V) as [n1|];
    destruct (pe_lookup pe_st2 V) as [n2|];
      try reflexivity; try solve_by_invert.
    rewrite negb_false_iff in Hagree.
    apply eqb_eq in Hagree. subst. reflexivity. Qed.

Fixpoint pe_removes (pe_st:pe_state) (ids : list string) : pe_state :=
  match ids with
  | [] => pe_st
  | V::ids => pe_remove (pe_removes pe_st ids) V
  end.

Theorem pe_removes_correct: forall pe_st ids V,
  pe_lookup (pe_removes pe_st ids) V =
  if inb String.eqb V ids then None else pe_lookup pe_st V.
Proof. intros pe_st ids V. induction ids as [| V' ids]. reflexivity.
  simpl. rewrite pe_remove_correct. rewrite IHids.
  compare V' V.
  - rewrite String.eqb_refl. reflexivity.
  - rewrite false_eqb_string; try congruence. reflexivity.
Qed.

Theorem pe_compare_removes: forall pe_st1 pe_st2 V,
  pe_lookup (pe_removes pe_st1 (pe_compare pe_st1 pe_st2)) V =
  pe_lookup (pe_removes pe_st2 (pe_compare pe_st1 pe_st2)) V.
Proof.
  intros pe_st1 pe_st2 V. rewrite !pe_removes_correct.
  destruct (inbP _ _ String.eqb_spec V (pe_compare pe_st1 pe_st2)).
  - reflexivity.
  - apply pe_compare_correct. auto. Qed.

Theorem pe_compare_update: forall pe_st1 pe_st2 st,
  pe_update st (pe_removes pe_st1 (pe_compare pe_st1 pe_st2)) =
  pe_update st (pe_removes pe_st2 (pe_compare pe_st1 pe_st2)).
Proof. intros. apply functional_extensionality. intros V.
  rewrite !pe_update_correct. rewrite pe_compare_removes. reflexivity.
Qed.

Fixpoint assign (pe_st : pe_state) (ids : list string) : com :=
  match ids with
  | [] => <{ skip }>
  | V::ids => match pe_lookup pe_st V with
              | Some n => <{ assign pe_st ids; V := n }>
              | None => assign pe_st ids
              end
  end.
  
Definition assigned (pe_st:pe_state) (ids : list string) (st:state) : state :=
  fun V => if inb String.eqb V ids then
                match pe_lookup pe_st V with
                | Some n => n
                | None => st V
                end
           else st V.

Theorem assign_removes: forall pe_st ids st,
  pe_update st pe_st =
  pe_update (assigned pe_st ids st) (pe_removes pe_st ids).
Proof. intros pe_st ids st. apply functional_extensionality. intros V.
  rewrite !pe_update_correct. rewrite pe_removes_correct. unfold assigned.
  destruct (inbP _ _ String.eqb_spec V ids); destruct (pe_lookup pe_st V); reflexivity.
Qed.

Lemma ceval_extensionality: forall c st st1 st2,
  st =[ c ]=> st1 -> (forall V, st1 V = st2 V) -> st =[ c ]=> st2.
Proof. intros c st st1 st2 H Heq.
  apply functional_extensionality in Heq. rewrite <- Heq. apply H. Qed.

Theorem eval_assign: forall pe_st ids st,
  st =[ assign pe_st ids ]=> assigned pe_st ids st.
Proof. intros pe_st ids st. induction ids as [| V ids]; simpl.
  - (*  *) eapply ceval_extensionality. apply E_Skip. reflexivity.
  - (* V::ids *)
    remember (pe_lookup pe_st V) as lookup. destruct lookup.
    + (* Some *) eapply E_Seq. apply IHids. unfold assigned. simpl.
      eapply ceval_extensionality. apply E_Asgn. simpl. reflexivity.
      intros V0. unfold t_update. compare V V0.
      * (* equal *) rewrite <- Heqlookup. rewrite String.eqb_refl. reflexivity.
      * (* not equal *) rewrite false_eqb_string; simpl; congruence.
    + (* None *) eapply ceval_extensionality. apply IHids.
      unfold assigned. intros V0. simpl. compare V V0.
      * (* equal *) rewrite <- Heqlookup.
        rewrite String.eqb_refl.
        destruct (inbP _ _ String.eqb_spec V ids); reflexivity.
      * (* not equal *) rewrite false_eqb_string; simpl; congruence.
Qed.

Reserved Notation "c1 '/' st '==>' c1' '/' st'"
  (at level 40, st at level 39, c1' at level 39).

Inductive pe_com : com -> pe_state -> com -> pe_state -> Prop :=
  | PE_Skip : forall pe_st,
      <{skip}> / pe_st ==> <{skip}> / pe_st
  | PE_AsgnStatic : forall pe_st a1 (n1 : nat) l,
      pe_aexp pe_st a1 = <{ n1 }> ->
      <{l := a1}> / pe_st ==> <{skip}> / pe_add pe_st l n1
  | PE_AsgnDynamic : forall pe_st a1 a1' l,
      pe_aexp pe_st a1 = a1' ->
      (forall n : nat , a1' <> <{ n }>) ->
      <{l := a1}> / pe_st ==> <{l := a1'}> / pe_remove pe_st l
  | PE_Seq : forall pe_st pe_st' pe_st'' c1 c2 c1' c2',
      c1 / pe_st ==> c1' / pe_st' ->
      c2 / pe_st' ==> c2' / pe_st'' ->
      <{c1 ; c2}> / pe_st ==> <{c1' ; c2'}> / pe_st''
  | PE_IfTrue : forall pe_st pe_st' b1 c1 c2 c1',
      pe_bexp pe_st b1 = <{ true }> ->
      c1 / pe_st ==> c1' / pe_st' ->
      <{if b1 then c1 else c2 end}> / pe_st ==> c1' / pe_st'
  | PE_IfFalse : forall pe_st pe_st' b1 c1 c2 c2',
      pe_bexp pe_st b1 = <{ false }> ->
      c2 / pe_st ==> c2' / pe_st' ->
      <{if b1 then c1 else c2 end}> / pe_st ==> c2' / pe_st'
  | PE_If : forall pe_st pe_st1 pe_st2 b1 c1 c2 c1' c2',
      pe_bexp pe_st b1 <> <{ true }> ->
      pe_bexp pe_st b1 <> <{ false }> ->
      c1 / pe_st ==> c1' / pe_st1 ->
      c2 / pe_st ==> c2' / pe_st2 ->
      <{if b1 then c1 else c2 end}> / pe_st
        ==> <{if pe_bexp pe_st b1
             then c1' ; assign pe_st1 (pe_compare pe_st1 pe_st2)
             else c2' ; assign pe_st2 (pe_compare pe_st1 pe_st2) end}>
            / pe_removes pe_st1 (pe_compare pe_st1 pe_st2)

  where "c1 '/' st '==>' c1' '/' st'" := (pe_com c1 st c1' st').
Local Hint Constructors pe_com : core.

Local Hint Constructors ceval : core.

Example pe_example1:
  <{X := 3 ; Y := Z * (X + X)}>
  / [] ==> <{skip; Y := Z * 6}> / [(X,3)].
Proof. eapply PE_Seq. eapply PE_AsgnStatic. simpl. reflexivity.
  eapply PE_AsgnDynamic. simpl. reflexivity. intros n H. inversion H.
Qed.

Example pe_example2:
  <{X := 3 ; if X <= 4 then X := 4 else skip end}>
  / [] ==> <{skip; skip}> / [(X,4)].
Proof. eapply PE_Seq. eapply PE_AsgnStatic. simpl. reflexivity.
  eapply PE_IfTrue. simpl. reflexivity.
  eapply PE_AsgnStatic. simpl. reflexivity.
Qed.

Example pe_example3:
  <{X := 3;
   if Y <= 4 then
     Y := 4;
     if X = Y then Y := 999 else skip end
   else skip end}> / []
  ==> <{skip;
       if Y <= 4 then
         (skip; skip); (skip; Y := 4)
       else skip; skip end}>
      / [(X,3)].
Proof. erewrite f_equal2 with (f := fun c st => _ / _ ==> c / st).
  eapply PE_Seq. eapply PE_AsgnStatic. reflexivity.
  eapply PE_If; intuition eauto; try solve_by_invert.
  econstructor. eapply PE_AsgnStatic. reflexivity.
  eapply PE_IfFalse. reflexivity. econstructor.
  reflexivity. reflexivity.
Qed.


Reserved Notation "c' '/' pe_st' '/' st '==>' st''"
  (at level 40, pe_st' at level 39, st at level 39).

Inductive pe_ceval
  (c':com) (pe_st':pe_state) (st:state) (st'':state) : Prop :=
  | pe_ceval_intro : forall st',
    st =[ c' ]=> st' ->
    pe_update st' pe_st' = st'' ->
    c' / pe_st' / st ==> st''
  where "c' '/' pe_st' '/' st '==>' st''" := (pe_ceval c' pe_st' st st'').
Local Hint Constructors pe_ceval : core.

Theorem pe_com_complete:
  forall c pe_st pe_st' c', c / pe_st ==> c' / pe_st' ->
  forall st st'',
  (pe_update st pe_st =[ c ]=> st'') ->
  (c' / pe_st' / st ==> st'').
Proof. intros c pe_st pe_st' c' Hpe.
  induction Hpe; intros st st'' Heval;
  try (inversion Heval; subst;
       try (rewrite -> pe_bexp_correct, -> H in *; solve_by_invert);
       []);
  eauto.
  - (* PE_AsgnStatic *) econstructor. econstructor.
    rewrite -> pe_aexp_correct. rewrite <- pe_update_update_add.
    rewrite -> H. reflexivity.
  - (* PE_AsgnDynamic *) econstructor. econstructor. reflexivity.
    rewrite -> pe_aexp_correct. rewrite <- pe_update_update_remove.
    reflexivity.
  - (* PE_Seq *)
    edestruct IHHpe1. eassumption. subst.
    edestruct IHHpe2. eassumption.
    eauto.
  - (* PE_If *) inversion Heval; subst.
    + (* E'IfTrue *) edestruct IHHpe1. eassumption.
      econstructor. apply E_IfTrue. rewrite <- pe_bexp_correct. assumption.
      eapply E_Seq. eassumption. apply eval_assign.
      rewrite <- assign_removes. eassumption.
    + (* E_IfFalse *) edestruct IHHpe2. eassumption.
      econstructor. apply E_IfFalse. rewrite <- pe_bexp_correct. assumption.
      eapply E_Seq. eassumption. apply eval_assign.
      rewrite -> pe_compare_update.
      rewrite <- assign_removes. eassumption.
Qed.

Theorem pe_com_sound:
  forall c pe_st pe_st' c', c / pe_st ==> c' / pe_st' ->
  forall st st'',
  (c' / pe_st' / st ==> st'') ->
  (pe_update st pe_st =[ c ]=> st'').
Proof. intros c pe_st pe_st' c' Hpe.
  induction Hpe;
    intros st st'' [st' Heval Heq];
    try (inversion Heval; []; subst); auto.
  - (* PE_AsgnStatic *) rewrite <- pe_update_update_add. apply E_Asgn.
    rewrite -> pe_aexp_correct. rewrite -> H. reflexivity.
  - (* PE_AsgnDynamic *) rewrite <- pe_update_update_remove. apply E_Asgn.
    rewrite <- pe_aexp_correct. reflexivity.
  - (* PE_Seq *) eapply E_Seq; eauto.
  - (* PE_IfTrue *) apply E_IfTrue.
    rewrite -> pe_bexp_correct. rewrite -> H. reflexivity. eauto.
  - (* PE_IfFalse *) apply E_IfFalse.
    rewrite -> pe_bexp_correct. rewrite -> H. reflexivity. eauto.
  - (* PE_If *)
    inversion Heval; subst; inversion H7;
      (eapply ceval_deterministic in H8; [| apply eval_assign]); subst.
    + (* E_IfTrue *)
      apply E_IfTrue. rewrite -> pe_bexp_correct. assumption.
      rewrite <- assign_removes. eauto.
    + (* E_IfFalse *)
      rewrite -> pe_compare_update.
      apply E_IfFalse. rewrite -> pe_bexp_correct. assumption.
      rewrite <- assign_removes. eauto.
Qed.

Corollary pe_com_correct:
  forall c pe_st pe_st' c', c / pe_st ==> c' / pe_st' ->
  forall st st'',
  (pe_update st pe_st =[ c ]=> st'') <->
  (c' / pe_st' / st ==> st'').
Proof. intros c pe_st pe_st' c' H st st''. split.
  - (* -> *) apply pe_com_complete. apply H.
  - (* <- *) apply pe_com_sound. apply H.
Qed.

Module Loop.

Reserved Notation "c1 '/' st '==>' c1' '/' st' '/' c''"
  (at level 40, st at level 39, c1' at level 39, st' at level 39).

Inductive pe_com : com -> pe_state -> com -> pe_state -> com -> Prop :=
  | PE_Skip : forall pe_st,
      <{ skip }> / pe_st ==> <{ skip }> / pe_st / <{skip}>
  | PE_AsgnStatic : forall pe_st a1 (n1 : nat) l,
      pe_aexp pe_st a1 = <{ n1 }> ->
      <{ l := a1 }> / pe_st ==> <{ skip }> / pe_add pe_st l n1 / <{skip}>
  | PE_AsgnDynamic : forall pe_st a1 a1' l,
      pe_aexp pe_st a1 = a1' ->
      (forall n : nat, a1' <> <{ n }> ) ->
      <{l := a1}> / pe_st ==> <{l := a1'}> / pe_remove pe_st l / <{skip}>
  | PE_Seq : forall pe_st pe_st' pe_st'' c1 c2 c1' c2' c'',
      c1 / pe_st ==> c1' / pe_st' / <{skip}> ->
      c2 / pe_st' ==> c2' / pe_st'' / c'' ->
      <{c1 ; c2}> / pe_st ==> <{c1' ; c2'}> / pe_st'' / c''
  | PE_IfTrue : forall pe_st pe_st' b1 c1 c2 c1' c'',
      pe_bexp pe_st b1 = <{ true }> ->
      c1 / pe_st ==> c1' / pe_st' / c'' ->
      <{if b1 then c1 else c2 end}> / pe_st ==> c1' / pe_st' / c''
  | PE_IfFalse : forall pe_st pe_st' b1 c1 c2 c2' c'',
      pe_bexp pe_st b1 = <{ false }> ->
      c2 / pe_st ==> c2' / pe_st' / c'' ->
      <{if b1 then c1 else c2 end}> / pe_st ==> c2' / pe_st' / c''
  | PE_If : forall pe_st pe_st1 pe_st2 b1 c1 c2 c1' c2' c'',
      pe_bexp pe_st b1 <> <{ true }> ->
      pe_bexp pe_st b1 <> <{ false }> ->
      c1 / pe_st ==> c1' / pe_st1 / c'' ->
      c2 / pe_st ==> c2' / pe_st2 / c'' ->
      <{if b1 then c1 else c2 end}> / pe_st
        ==> <{if pe_bexp pe_st b1
             then c1' ; assign pe_st1 (pe_compare pe_st1 pe_st2)
             else c2' ; assign pe_st2 (pe_compare pe_st1 pe_st2) end}>
            / pe_removes pe_st1 (pe_compare pe_st1 pe_st2)
            / c''
  | PE_WhileFalse : forall pe_st b1 c1,
      pe_bexp pe_st b1 = <{ false }> ->
      <{while b1 do c1 end}> / pe_st ==> <{skip}> / pe_st / <{skip}>
  | PE_WhileTrue : forall pe_st pe_st' pe_st'' b1 c1 c1' c2' c2'',
      pe_bexp pe_st b1 = <{ true }> ->
      c1 / pe_st ==> c1' / pe_st' / <{skip}> ->
      <{while b1 do c1 end}> / pe_st' ==> c2' / pe_st'' / c2'' ->
      pe_compare pe_st pe_st'' <> [] ->
      <{while b1 do c1 end}> / pe_st ==> <{c1';c2'}> / pe_st'' / c2''
  | PE_While : forall pe_st pe_st' pe_st'' b1 c1 c1' c2' c2'',
      pe_bexp pe_st b1 <> <{ false }> ->
      pe_bexp pe_st b1 <> <{ true }> ->
      c1 / pe_st ==> c1' / pe_st' / <{skip}> ->
      <{while b1 do c1 end}> / pe_st' ==> c2' / pe_st'' / c2'' ->
      pe_compare pe_st pe_st'' <> [] ->
      (c2'' = <{skip}> \/ c2'' = <{while b1 do c1 end}>) ->
      <{while b1 do c1 end}> / pe_st
        ==> <{if pe_bexp pe_st b1
             then c1'; c2'; assign pe_st'' (pe_compare pe_st pe_st'')
             else assign pe_st (pe_compare pe_st pe_st'') end}>
            / pe_removes pe_st (pe_compare pe_st pe_st'')
            / c2''
  | PE_WhileFixedEnd : forall pe_st b1 c1,
      pe_bexp pe_st b1 <> <{ false }> ->
      <{while b1 do c1 end}> / pe_st ==> <{skip}> / pe_st / <{while b1 do c1 end}>
  | PE_WhileFixedLoop : forall pe_st pe_st' pe_st'' b1 c1 c1' c2',
      pe_bexp pe_st b1 = <{ true }> ->
      c1 / pe_st ==> c1' / pe_st' / <{skip}> ->
      <{while b1 do c1 end}> / pe_st'
        ==> c2' / pe_st'' / <{while b1 do c1 end}>->
      pe_compare pe_st pe_st'' = [] ->
      <{while b1 do c1 end}> / pe_st
        ==> <{while true do skip end}> / pe_st / <{skip}>
      (* Because we have an infinite loop, we should actually
         start to throw away the rest of the program:
         (while b1 do c1 end) / pe_st
         ==> skip / pe_st / (while true do skip end) *)
  | PE_WhileFixed : forall pe_st pe_st' pe_st'' b1 c1 c1' c2',
      pe_bexp pe_st b1 <> <{ false }> ->
      pe_bexp pe_st b1 <> <{ true }> ->
      c1 / pe_st ==> c1' / pe_st' / <{skip}> ->
      <{while b1 do c1 end}> / pe_st'
        ==> c2' / pe_st'' / <{while b1 do c1 end}> ->
      pe_compare pe_st pe_st'' = [] ->
      <{while b1 do c1 end}> / pe_st
        ==> <{while pe_bexp pe_st b1 do c1'; c2' end}> / pe_st / <{skip}>

  where "c1 '/' st '==>' c1' '/' st' '/' c''" := (pe_com c1 st c1' st' c'').
Local Hint Constructors pe_com : core.
Ltac step i :=
  (eapply i; intuition eauto; try solve_by_invert);
  repeat (try eapply PE_Seq;
          try (eapply PE_AsgnStatic; simpl; reflexivity);
          try (eapply PE_AsgnDynamic;
               [ simpl; reflexivity
               | intuition eauto; solve_by_invert])).
               
Definition square_loop: com :=
  <{while 1 <= X do
    Y := Y * Y;
    X := X - 1
  end}>.

Example pe_loop_example1:
  square_loop / []
  ==> <{while 1 <= X do
         (Y := Y * Y;
          X := X - 1); skip
       end}> / [] / <{skip}>.
Proof. erewrite f_equal2 with (f := fun c st => _ / _ ==> c / st / <{skip}>).
  step PE_WhileFixed. step PE_WhileFixedEnd. reflexivity.
  reflexivity. reflexivity. Qed.
Example pe_loop_example2:
  <{X := 3; square_loop}> / []
  ==> <{skip;
       (Y := Y * Y; skip);
       (Y := Y * Y; skip);
       (Y := Y * Y; skip);
       skip}> / [(X,0)] / <{skip}>.
Proof. erewrite f_equal2 with (f := fun c st => _ / _ ==> c / st / <{skip}>).
  eapply PE_Seq. eapply PE_AsgnStatic. reflexivity.
  step PE_WhileTrue.
  step PE_WhileTrue.
  step PE_WhileTrue.
  step PE_WhileFalse.
  inversion H. inversion H. inversion H.
  reflexivity. reflexivity. Qed.
Example pe_loop_example3:
  <{Z := 3; subtract_slowly}> / []
  ==> <{skip;
       if X <> 0 then
         (skip; X := X - 1);
         if X <> 0 then
           (skip; X := X - 1);
           if X <> 0 then
             (skip; X := X - 1);
             while X <> 0 do
               (skip; X := X - 1); skip
             end;
             skip; Z := 0
           else skip; Z := 1 end; skip
         else skip; Z := 2 end; skip
       else skip; Z := 3 end}> / [] / <{skip}>.
Proof. erewrite f_equal2 with (f := fun c st => _ / _ ==> c / st / <{skip}>).
  eapply PE_Seq. eapply PE_AsgnStatic. reflexivity.
  step PE_While.
  step PE_While.
  step PE_While.
  step PE_WhileFixed.
  step PE_WhileFixedEnd.
  reflexivity. inversion H. inversion H. inversion H.
  reflexivity. reflexivity. Qed.
Example pe_loop_example4:
  <{X := 0;
   while X <= 2 do
     X := 1 - X
   end}> / [] ==> <{skip; while true do skip end}> / [(X,0)] / <{skip}>.
Proof. erewrite f_equal2 with (f := fun c st => _ / _ ==> c / st / <{skip}>).
  eapply PE_Seq. eapply PE_AsgnStatic. reflexivity.
  step PE_WhileFixedLoop.
  step PE_WhileTrue.
  step PE_WhileFixedEnd.
  inversion H. reflexivity. reflexivity. reflexivity.
Qed.

Reserved Notation "c1 '/' st '==>' st' '#' n"
  (at level 40, st at level 39, st' at level 39).
Inductive ceval_count : com -> state -> state -> nat -> Prop :=
  | E'Skip : forall st,
      <{skip}> / st ==> st # 0
  | E'Asgn : forall st a1 n l,
      aeval st a1 = n ->
      <{l := a1}> / st ==> (t_update st l n) # 0
  | E'Seq : forall c1 c2 st st' st'' n1 n2,
      c1 / st ==> st' # n1 ->
      c2 / st' ==> st'' # n2 ->
      <{c1 ; c2}> / st ==> st'' # (n1 + n2)
  | E'IfTrue : forall st st' b1 c1 c2 n,
      beval st b1 = true ->
      c1 / st ==> st' # n ->
      <{if b1 then c1 else c2 end}> / st ==> st' # n
  | E'IfFalse : forall st st' b1 c1 c2 n,
      beval st b1 = false ->
      c2 / st ==> st' # n ->
      <{if b1 then c1 else c2 end}> / st ==> st' # n
  | E'WhileFalse : forall b1 st c1,
      beval st b1 = false ->
      <{while b1 do c1 end}> / st ==> st # 0
  | E'WhileTrue : forall st st' st'' b1 c1 n1 n2,
      beval st b1 = true ->
      c1 / st ==> st' # n1 ->
      <{while b1 do c1 end}> / st' ==> st'' # n2 ->
      <{while b1 do c1 end}> / st ==> st'' # S (n1 + n2)

  where "c1 '/' st '==>' st' # n" := (ceval_count c1 st st' n).
Local Hint Constructors ceval_count : core.
Theorem ceval_count_complete: forall c st st',
  st =[ c ]=> st' -> exists n, c / st ==> st' # n.
Proof. intros c st st' Heval.
  induction Heval;
    try inversion IHHeval1;
    try inversion IHHeval2;
    try inversion IHHeval;
    eauto. Qed.
Theorem ceval_count_sound: forall c st st' n,
  c / st ==> st' # n -> st =[ c ]=> st'.
Proof. intros c st st' n Heval. induction Heval; eauto. Qed.
Theorem pe_compare_nil_lookup: forall pe_st1 pe_st2,
  pe_compare pe_st1 pe_st2 = [] ->
  forall V, pe_lookup pe_st1 V = pe_lookup pe_st2 V.
Proof. intros pe_st1 pe_st2 H V.
  apply (pe_compare_correct pe_st1 pe_st2 V).
  rewrite H. intro. inversion H0. Qed.
Theorem pe_compare_nil_update: forall pe_st1 pe_st2,
  pe_compare pe_st1 pe_st2 = [] ->
  forall st, pe_update st pe_st1 = pe_update st pe_st2.
Proof. intros pe_st1 pe_st2 H st.
  apply functional_extensionality. intros V.
  rewrite !pe_update_correct.
  apply pe_compare_nil_lookup with (V:=V) in H.
  rewrite H. reflexivity. Qed.
  
Reserved Notation "c' '/' pe_st' '/' c'' '/' st '==>' st'' '#' n"
  (at level 40, pe_st' at level 39, c'' at level 39,
   st at level 39, st'' at level 39).

Inductive pe_ceval_count (c':com) (pe_st':pe_state) (c'':com)
                         (st:state) (st'':state) (n:nat) : Prop :=
  | pe_ceval_count_intro : forall st' n',
    st =[ c' ]=> st' ->
    c'' / pe_update st' pe_st' ==> st'' # n' ->
    n' <= n ->
    c' / pe_st' / c'' / st ==> st'' # n
  where "c' '/' pe_st' '/' c'' '/' st '==>' st'' '#' n" :=
        (pe_ceval_count c' pe_st' c'' st st'' n).
Local Hint Constructors pe_ceval_count : core.
Lemma pe_ceval_count_le: forall c' pe_st' c'' st st'' n n',
  n' <= n ->
  c' / pe_st' / c'' / st ==> st'' # n' ->
  c' / pe_st' / c'' / st ==> st'' # n.
Proof. intros c' pe_st' c'' st st'' n n' Hle H. inversion H.
  econstructor; try eassumption. lia. Qed.
Theorem pe_com_complete:
  forall c pe_st pe_st' c' c'', c / pe_st ==> c' / pe_st' / c'' ->
  forall st st'' n,
  (c / pe_update st pe_st ==> st'' # n) ->
  (c' / pe_st' / c'' / st ==> st'' # n).
Proof. intros c pe_st pe_st' c' c'' Hpe.
  induction Hpe; intros st st'' n Heval;
  try (inversion Heval; subst;
       try (rewrite -> pe_bexp_correct, -> H in *; solve_by_invert);
       []);
  eauto.
  - (* PE_AsgnStatic *) econstructor. econstructor.
    rewrite -> pe_aexp_correct. rewrite <- pe_update_update_add.
    rewrite -> H. apply E'Skip. auto.
  - (* PE_AsgnDynamic *) econstructor. econstructor. reflexivity.
    rewrite -> pe_aexp_correct. rewrite <- pe_update_update_remove.
    apply E'Skip. auto.
  - (* PE_Seq *)
    edestruct IHHpe1 as [? ? ? Hskip ?]. eassumption.
    inversion Hskip. subst.
    edestruct IHHpe2. eassumption.
    econstructor; eauto. lia.
  - (* PE_If *) inversion Heval; subst.
    + (* E'IfTrue *) edestruct IHHpe1. eassumption.
      econstructor. apply E_IfTrue. rewrite <- pe_bexp_correct. assumption.
      eapply E_Seq. eassumption. apply eval_assign.
      rewrite <- assign_removes. eassumption. eassumption.
    + (* E_IfFalse *) edestruct IHHpe2. eassumption.
      econstructor. apply E_IfFalse. rewrite <- pe_bexp_correct. assumption.
      eapply E_Seq. eassumption. apply eval_assign.
      rewrite -> pe_compare_update.
      rewrite <- assign_removes. eassumption. eassumption.
  - (* PE_WhileTrue *)
    edestruct IHHpe1 as [? ? ? Hskip ?]. eassumption.
    inversion Hskip. subst.
    edestruct IHHpe2. eassumption.
    econstructor; eauto. lia.
  - (* PE_While *) inversion Heval; subst.
    + (* E_WhileFalse *) econstructor. apply E_IfFalse.
      rewrite <- pe_bexp_correct. assumption.
      apply eval_assign.
      rewrite <- assign_removes. inversion H2; subst; auto.
      auto.
    + (* E_WhileTrue *)
      edestruct IHHpe1 as [? ? ? Hskip ?]. eassumption.
      inversion Hskip. subst.
      edestruct IHHpe2. eassumption.
      econstructor. apply E_IfTrue.
      rewrite <- pe_bexp_correct. assumption.
      repeat eapply E_Seq; eauto. apply eval_assign.
      rewrite -> pe_compare_update, <- assign_removes. eassumption.
      lia.
  - (* PE_WhileFixedLoop *) exfalso.
    generalize dependent (S (n1 + n2)). intros n.
    clear - H H0 IHHpe1 IHHpe2. generalize dependent st.
    induction n using lt_wf_ind; intros st Heval. inversion Heval; subst.
    + (* E'WhileFalse *) rewrite pe_bexp_correct, H in H7. inversion H7.
    + (* E'WhileTrue *)
      edestruct IHHpe1 as [? ? ? Hskip ?]. eassumption.
      inversion Hskip. subst.
      edestruct IHHpe2. eassumption.
      rewrite <- (pe_compare_nil_update _ _ H0) in H7.
      apply H1 in H7; [| lia]. inversion H7.
  - (* PE_WhileFixed *) generalize dependent st.
    induction n using lt_wf_ind; intros st Heval. inversion Heval; subst.
    + (* E'WhileFalse *) rewrite pe_bexp_correct in H8. eauto.
    + (* E'WhileTrue *) rewrite pe_bexp_correct in H5.
      edestruct IHHpe1 as [? ? ? Hskip ?]. eassumption.
      inversion Hskip. subst.
      edestruct IHHpe2. eassumption.
      rewrite <- (pe_compare_nil_update _ _ H1) in H8.
      apply H2 in H8; [| lia]. inversion H8.
      econstructor; [ eapply E_WhileTrue; eauto | eassumption | lia].
Qed.
Theorem pe_com_sound:
  forall c pe_st pe_st' c' c'', c / pe_st ==> c' / pe_st' / c'' ->
  forall st st'' n,
  (c' / pe_st' / c'' / st ==> st'' # n) ->
  (pe_update st pe_st =[ c ]=> st'').
Proof. intros c pe_st pe_st' c' c'' Hpe.
  induction Hpe;
    intros st st'' n [st' n' Heval Heval' Hle];
    try (inversion Heval; []; subst);
    try (inversion Heval'; []; subst); eauto.
  - (* PE_AsgnStatic *) rewrite <- pe_update_update_add. apply E_Asgn.
    rewrite -> pe_aexp_correct. rewrite -> H. reflexivity.
  - (* PE_AsgnDynamic *) rewrite <- pe_update_update_remove. apply E_Asgn.
    rewrite <- pe_aexp_correct. reflexivity.
  - (* PE_Seq *) eapply E_Seq; eauto.
  - (* PE_IfTrue *) apply E_IfTrue.
    rewrite -> pe_bexp_correct. rewrite -> H. reflexivity.
    eapply IHHpe. eauto.
  - (* PE_IfFalse *) apply E_IfFalse.
    rewrite -> pe_bexp_correct. rewrite -> H. reflexivity.
    eapply IHHpe. eauto.
  - (* PE_If *) inversion Heval; subst; inversion H7; subst; clear H7.
    + (* E_IfTrue *)
      eapply ceval_deterministic in H8; [| apply eval_assign]. subst.
      rewrite <- assign_removes in Heval'.
      apply E_IfTrue. rewrite -> pe_bexp_correct. assumption.
      eapply IHHpe1. eauto.
    + (* E_IfFalse *)
      eapply ceval_deterministic in H8; [| apply eval_assign]. subst.
      rewrite -> pe_compare_update in Heval'.
      rewrite <- assign_removes in Heval'.
      apply E_IfFalse. rewrite -> pe_bexp_correct. assumption.
      eapply IHHpe2. eauto.
  - (* PE_WhileFalse *) apply E_WhileFalse.
    rewrite -> pe_bexp_correct. rewrite -> H. reflexivity.
  - (* PE_WhileTrue *) eapply E_WhileTrue.
    rewrite -> pe_bexp_correct. rewrite -> H. reflexivity.
    eapply IHHpe1. eauto. eapply IHHpe2. eauto.
  - (* PE_While *) inversion Heval; subst.
    + (* E_IfTrue *)
      inversion H9. subst. clear H9.
      inversion H10. subst. clear H10.
      eapply ceval_deterministic in H11; [| apply eval_assign]. subst.
      rewrite -> pe_compare_update in Heval'.
      rewrite <- assign_removes in Heval'.
      eapply E_WhileTrue. rewrite -> pe_bexp_correct. assumption.
      eapply IHHpe1. eauto.
      eapply IHHpe2. eauto.
    + (* E_IfFalse *) apply ceval_count_sound in Heval'.
      eapply ceval_deterministic in H9; [| apply eval_assign]. subst.
      rewrite <- assign_removes in Heval'.
      inversion H2; subst.
      * (* c2'' = skip *) inversion Heval'. subst. apply E_WhileFalse.
        rewrite -> pe_bexp_correct. assumption.
      * (* c2'' = while b1 do c1 end *) assumption.
  - (* PE_WhileFixedEnd *) eapply ceval_count_sound. apply Heval'.
  - (* PE_WhileFixedLoop *)
    apply loop_never_stops in Heval. inversion Heval.
  - (* PE_WhileFixed *)
    clear - H1 IHHpe1 IHHpe2 Heval.
    remember <{while pe_bexp pe_st b1 do c1'; c2' end}> as c'.
    induction Heval;
      inversion Heqc'; subst; clear Heqc'.
    + (* E_WhileFalse *) apply E_WhileFalse.
      rewrite pe_bexp_correct. assumption.
    + (* E_WhileTrue *)
      assert (IHHeval2' := IHHeval2 (refl_equal _)).
      apply ceval_count_complete in IHHeval2'. inversion IHHeval2'.
      clear IHHeval1 IHHeval2 IHHeval2'.
      inversion Heval1. subst.
      eapply E_WhileTrue. rewrite pe_bexp_correct. assumption. eauto.
      eapply IHHpe2. econstructor. eassumption.
      rewrite <- (pe_compare_nil_update _ _ H1). eassumption. apply le_n.
Qed.
Corollary pe_com_correct:
  forall c pe_st pe_st' c', c / pe_st ==> c' / pe_st' / <{skip}> ->
  forall st st'',
  (pe_update st pe_st =[ c ]=> st'') <->
  (exists st', st =[ c' ]=> st' /\ pe_update st' pe_st' = st'').
Proof. intros c pe_st pe_st' c' H st st''. split.
  - (* -> *) intros Heval.
    apply ceval_count_complete in Heval. inversion Heval as [n Heval'].
    apply pe_com_complete with (st:=st) (st'':=st'') (n:=n) in H.
    inversion H as [? ? ? Hskip ?]. inversion Hskip. subst. eauto.
    assumption.
  - (* <- *) intros [st' [Heval Heq] ]. subst st''.
    eapply pe_com_sound in H. apply H.
    econstructor. apply Heval. apply E'Skip. apply le_n.
Qed.
End Loop.

Inductive block (Label:Type) : Type :=
  | Goto : Label -> block Label
  | If : bexp -> Label -> Label -> block Label
  | Assign : string -> aexp -> block Label -> block Label.
  
Arguments Goto {Label} _.
Arguments If {Label} _ _ _.
Arguments Assign {Label} _ _ _.

Inductive parity_label : Type :=
  | entry : parity_label
  | loop : parity_label
  | body : parity_label
  | done : parity_label.
  
Definition parity_body : block parity_label :=
  Assign Y <{Y - 1}>
   (Assign X <{1 - X}>
     (Goto loop)).
     
Fixpoint keval {L:Type} (st:state) (k: block L) : state * L :=
  match k with
  | Goto l => (st, l)
  | If b l1 l2 => (st, if beval st b then l1 else l2)
  | Assign i a k => keval (t_update st i (aeval st a)) k
  end.

Example keval_example:
  keval empty_st parity_body
  = ((X !-> 1 ; Y !-> 0), loop).
Proof. reflexivity. Qed.

Definition program (L:Type) : Type := L -> option (block L).

Definition parity : program parity_label := fun l =>
  match l with 
  | entry => Some (Assign X 0 (Goto loop))
  | loop => Some (If <{ 1 <= Y }> body done)
  | body => Some parity_body
  | done => None (* Halt *)
  end.
  
Inductive peval {L:Type} (p:program L)
  : state -> L -> state -> L -> Prop :=
  | E_None : forall st l,
    p l = None ->
    peval p st l st l
  | E_Some : forall st l k st' l' st'' l'',
    p l = Some k ->
    keval st k = (st', l') ->
    peval p st' l' st'' l'' ->
    peval p st l st'' l''.
    
Example parity_eval: peval parity empty_st entry empty_st done.
Proof. erewrite f_equal with (f := fun st => peval _ _ _ st _).
  eapply E_Some. reflexivity. reflexivity.
  eapply E_Some. reflexivity. reflexivity.
  apply E_None. reflexivity.
  apply functional_extensionality. intros i. rewrite t_update_same; auto.
Qed.

Fixpoint pe_block {L:Type} (pe_st:pe_state) (k : block L)
  : block (pe_state * L) :=
  match k with
  | Goto l => Goto (pe_st, l)
  | If b l1 l2 =>
    match pe_bexp pe_st b with
    | BTrue => Goto (pe_st, l1)
    | BFalse => Goto (pe_st, l2)
    | b' => If b' (pe_st, l1) (pe_st, l2)
    end
  | Assign i a k =>
    match pe_aexp pe_st a with
    | ANum n => pe_block (pe_add pe_st i n) k
    | a' => Assign i a' (pe_block (pe_remove pe_st i) k)
    end
  end.
Example pe_block_example:
  pe_block [(X,0)] parity_body
  = Assign Y <{Y - 1}> (Goto ([(X,1)], loop)).
Proof. reflexivity. Qed.

Theorem pe_block_correct: forall (L:Type) st pe_st k st' pe_st' (l':L),
  keval st (pe_block pe_st k) = (st', (pe_st', l')) ->
  keval (pe_update st pe_st) k = (pe_update st' pe_st', l').
Proof. intros. generalize dependent pe_st. generalize dependent st.
  induction k as [l | b l1 l2 | i a k];
    intros st pe_st H.
  - (* Goto *) inversion H; reflexivity.
  - (* If *)
    replace (keval st (pe_block pe_st (If b l1 l2)))
       with (keval st (If (pe_bexp pe_st b) (pe_st, l1) (pe_st, l2)))
       in H by (simpl; destruct (pe_bexp pe_st b); reflexivity).
    simpl in *. rewrite pe_bexp_correct.
    destruct (beval st (pe_bexp pe_st b)); inversion H; reflexivity.
  - (* Assign *)
    simpl in *. rewrite pe_aexp_correct.
    destruct (pe_aexp pe_st a); simpl;
      try solve [rewrite pe_update_update_add; apply IHk; apply H];
      solve [rewrite pe_update_update_remove; apply IHk; apply H].
Qed.
Definition pe_program {L:Type} (p : program L)
  : program (pe_state * L) :=
  fun pe_l => match pe_l with | (pe_st, l) =>
                option_map (pe_block pe_st) (p l)
              end.
Inductive pe_peval {L:Type} (p : program L)
  (st:state) (pe_st:pe_state) (l:L) (st'o:state) (l':L) : Prop :=
  | pe_peval_intro : forall st' pe_st',
    peval (pe_program p) st (pe_st, l) st' (pe_st', l') ->
    pe_update st' pe_st' = st'o ->
    pe_peval p st pe_st l st'o l'.

Theorem pe_program_correct:
  forall (L:Type) (p : program L) st pe_st l st'o l',
  peval p (pe_update st pe_st) l st'o l' <->
  pe_peval p st pe_st l st'o l'.
Proof. intros.
  split.
  - (* -> *) intros Heval.
    remember (pe_update st pe_st) as sto.
    generalize dependent pe_st. generalize dependent st.
    induction Heval as
      [ sto l Hlookup | sto l k st'o l' st''o l'' Hlookup Hkeval Heval ];
      intros st pe_st Heqsto; subst sto.
    + (* E_None *) eapply pe_peval_intro. apply E_None.
      simpl. rewrite Hlookup. reflexivity. reflexivity.
    + (* E_Some *)
      remember (keval st (pe_block pe_st k)) as x.
      destruct x as [st' [pe_st' l'_] ].
      symmetry in Heqx. erewrite pe_block_correct in Hkeval by apply Heqx.
      inversion Hkeval. subst st'o l'_. clear Hkeval.
      edestruct IHHeval. reflexivity. subst st''o. clear IHHeval.
      eapply pe_peval_intro; [| reflexivity]. eapply E_Some; eauto.
      simpl. rewrite Hlookup. reflexivity.
  - (* <- *) intros [st' pe_st' Heval Heqst'o].
    remember (pe_st, l) as pe_st_l.
    remember (pe_st', l') as pe_st'_l'.
    generalize dependent pe_st. generalize dependent l.
    induction Heval as
      [ st [pe_st_ l_] Hlookup
      | st [pe_st_ l_] pe_k st' [pe_st'_ l'_] st'' [pe_st'' l'']
        Hlookup Hkeval Heval ];
      intros l pe_st Heqpe_st_l;
      inversion Heqpe_st_l; inversion Heqpe_st'_l'; repeat subst.
    + (* E_None *) apply E_None. simpl in Hlookup.
      destruct (p l'); [ solve [ inversion Hlookup ] | reflexivity ].
    + (* E_Some *)
      simpl in Hlookup. remember (p l) as k.
      destruct k as [k|]; inversion Hlookup; subst.
      eapply E_Some; eauto. apply pe_block_correct. apply Hkeval.
Qed.