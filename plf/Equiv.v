Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Logic.FunctionalExtensionality.
From PLF Require Export Imp.
Set Default Goal Selector "!".

Definition aequiv (a1 a2 : aexp) : Prop := 
  forall (st : state), aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop := 
  forall (st : state), beval st b1 = beval st b2.

Theorem  aequiv_example :
  aequiv
    <{ X - X }>
    <{ 0 }>.
Proof.
  intros st. simpl. lia.  
Qed.

Theorem bequiv_example:
  bequiv
    <{ X - X = 0}>
    <{ true }>.
Proof.
  intros st. unfold beval. rewrite aequiv_example. reflexivity.
Qed.

Definition cequiv (c1 c2 : com) : Prop := 
  forall (st st' : state),
  (st =[ c1 ]=> st') <-> (st =[ c2 ]=> st').

Definition refines (c1 c2 : com) : Prop := 
  forall (st st' : state),
  (st =[ c1 ]=> st') -> (st =[ c2 ]=> st').
  
Theorem skip_left : forall c,
  cequiv
    <{ skip; c }>
    c .
Proof.
  intros c st st'.
  split; intros H.
  - inversion H. subst.
    inversion H2. subst.
    assumption.
  - apply E_Seq with st.
    + apply E_Skip.
    + assumption.
Qed.

Theorem skip_right : forall c,
  cequiv
    <{ c; skip }>
    c .
Proof.
  intros c st st'.
  split; intros H.
  - inversion H. inversion H5. subst. assumption.
  - apply E_Seq with st'.
    + assumption.
    + apply E_Skip.
Qed.

Theorem if_true : forall b c1 c2,
  bequiv b <{ true }> ->
  cequiv <{ if b then c1 else c2 end }>
  c1.
Proof.
  intros b c1 c2 Hb.
  split; intros.
  - inversion H; subst.
    + assumption.
    + unfold bequiv in Hb. simpl in Hb.
      rewrite Hb in H5.
      discriminate.
  - apply E_IfTrue; try assumption.
    unfold bequiv in Hb. simpl in Hb. apply Hb.
Qed.

Theorem if_false : forall b c1 c2,
  bequiv b <{ false }> ->
  cequiv <{ if b then c1 else c2 end }>
  c2.
Proof.
  intros b c1 c2 Hb.
  split; intros.
  - inversion H; subst; unfold bequiv in Hb; simpl in Hb; rewrite Hb in H5.
    + discriminate.
    + assumption.
  - apply E_IfFalse; try assumption.
    unfold bequiv in Hb. simpl in Hb. apply Hb.
Qed.

Theorem swap_if_branches : forall b c1 c2,
  cequiv
    <{ if b then c1 else c2 end }>
    <{ if ~ b then c2 else c1 end }>.
Proof.
  unfold cequiv. intros.
  split; intros.
  - inversion H; subst.
    + apply E_IfFalse.
      * simpl. rewrite H5. reflexivity.
      * assumption.
    + apply E_IfTrue.
      * simpl. rewrite H5. reflexivity.
      * assumption.
  - inversion H; subst.
    + apply E_IfFalse.
      * simpl in H5. rewrite negb_true_iff in H5. assumption.
      * simpl in H5. rewrite negb_true_iff in H5. assumption.
    + apply E_IfTrue.
      * simpl in H5. rewrite negb_false_iff in H5. assumption.
      * assumption.
Qed.

Theorem while_false : forall b c,
  bequiv b <{false}> ->
  cequiv
    <{ while b do c end }>
    <{ skip }>.
Proof.
  intros b c Hb. split; intros H.
  - inversion H; subst.
    + apply E_Skip.
    + rewrite Hb in H2. discriminate.
  - inversion H; subst.
    + apply E_WhileFalse. apply Hb.
Qed.

Lemma while_true_nonterm : forall b c st st',
  bequiv b <{ true }> -> 
  ~ (st =[ while b do c end ]=> st').
Proof.
  intros b c st st' Hb.
  intros H.
  remember <{ while b do c end }> as cw eqn:Heqcw.
  induction H; inversion Heqcw; subst; clear Heqcw.
  - unfold bequiv in Hb. rewrite Hb in H. discriminate.
  - apply IHceval2. reflexivity.
Qed.

Theorem while_true : forall b c,
  bequiv b <{true}> ->
  cequiv
    <{ while b do c end }>
    <{ while true do skip end }>.
Proof.
  intros b c Hb. split; intros H; 
  exfalso; generalize dependent H; apply while_true_nonterm.
  - assumption.
  - unfold bequiv. reflexivity.
Qed.

Theorem loop_unrolling : forall b c,
  cequiv
    <{ while b do c end }>
    <{ if b then c ; while b do c end else skip end }>.
Proof.
  intros b c st st'.
  split; intros Hce.
  - inversion Hce; subst.
    * apply E_IfFalse.
      -- assumption.
      -- apply E_Skip.
    * apply E_IfTrue.
      -- assumption.
      -- apply E_Seq with (st' := st'0); assumption.
  - inversion Hce; subst.
    + inversion H5; subst.
      apply E_WhileTrue with (st' := st'0); assumption.
    + inversion H5; subst. apply E_WhileFalse. assumption.
Qed.

Theorem seq_assoc : forall c1 c2 c3,
  cequiv <{(c1;c2);c3}> <{c1;(c2;c3)}>.
Proof.
  intros c1 c2 c3 st st'.
  split; intros Hce.
  - inversion Hce; subst. inversion H1; subst.
    apply E_Seq with (st' := st'1).
    + assumption.
    + apply E_Seq with (st' := st'0).
      * assumption.
      * assumption.
  - inversion Hce; subst.
    inversion H4; subst.
    apply E_Seq with (st' := st'1).
    + apply E_Seq with (st' := st'0).
      * assumption.
      * assumption.
    + assumption.
Qed.

Theorem identity_assignment : forall x,
  cequiv
    <{ x := x }>
    <{ skip }>.
Proof.
  intros.
  split; intro H; inversion H; subst; clear H.
  - (* -> *)
    rewrite t_update_same.
    apply E_Skip.
  - (* <- *)
    assert (Hx : st' =[ x := x ]=> (x !-> st' x ; st')).
    { apply E_Asgn. reflexivity. }
    rewrite t_update_same in Hx.
    apply Hx.
Qed.
    
Theorem assign_aequiv : forall (X : string) (a : aexp),
  aequiv <{ X }> a ->
  cequiv <{ skip }> <{ X := a }>.
Proof.
  unfold aequiv. intros X a Ha st st'. split; intro H; inversion H; subst; clear H.
  Admitted.

Definition prog_a : com :=
  <{ while ~(X <= 0) do
       X := X + 1
     end }>.

Definition prog_b : com :=
  <{ if (X = 0) then
       X := X + 1;
       Y := 1
     else
       Y := 0
     end;
     X := X - Y;
     Y := 0 }>.

Definition prog_c : com :=
  <{ skip }> .
Definition prog_d : com :=
  <{ while X <> 0 do
       X := (X * Y) + 1
     end }>.
Definition prog_e : com :=
  <{ Y := 0 }>.
Definition prog_f : com :=
  <{ Y := X + 1;
     while X <> Y do
       Y := X + 1
     end }>.
Definition prog_g : com :=
  <{ while true do
       skip
     end }>.
  Definition prog_h : com :=
    <{ while X <> X do
         X := X + 1
       end }>.
  Definition prog_i : com :=
    <{ while X <> Y do
         X := Y + 1
       end }>.
Definition equiv_classes : list (list com) :=
[].

Lemma refl_aequv : forall (a : aexp),
  aequiv a a.
Proof.
  intros a st. reflexivity.
Qed.

Lemma sym_aequiv : forall (a1 a2 : aexp),
  aequiv a1 a2 -> aequiv a2 a1.
Proof.
  intros a1 a2 H. intros st. symmetry. apply H. Qed.

Lemma trans_aequiv : forall (a1 a2 a3 : aexp),
  aequiv a1 a2 -> aequiv a2 a3 -> aequiv a1 a3.
Proof.
  unfold aequiv. intros a1 a2 a3 H12 H23 st.
  rewrite H12. rewrite H23. reflexivity.
Qed.

Lemma refl_bequiv : forall (b : bexp),
  bequiv b b.
Proof.
  unfold bequiv. intros b st. reflexivity.
Qed.

Lemma sym_bequiv : forall (b1 b2 : bexp),
  bequiv b1 b2 -> bequiv b2 b1.
Proof.
  unfold bequiv. intros b1 b2 H. intros st. symmetry. apply H. Qed.

Lemma trans_bequiv : forall (b1 b2 b3 : bexp),
  bequiv b1 b2 -> bequiv b2 b3 -> bequiv b1 b3.
Proof.
  unfold bequiv. intros b1 b2 b3 H12 H23 st.
  rewrite H12. rewrite H23. reflexivity.
Qed.

Lemma refl_cequiv : forall (c : com),
  cequiv c c.
Proof.
  unfold cequiv. intros c st st'. reflexivity.
Qed.

Lemma sym_cequiv : forall (c1 c2 : com),
  cequiv c1 c2 -> cequiv c2 c1.
Proof.
  unfold cequiv. intros c1 c2 H st st'.
  rewrite H. reflexivity.
Qed.

Lemma trans_cequiv : forall (c1 c2 c3 : com),
  cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
Proof.
  unfold cequiv. intros c1 c2 c3 H12 H23 st st'.
  rewrite H12. apply H23.
Qed.

Theorem CAsgn_congruence : forall x a a',
  aequiv a a' ->
  cequiv <{x := a}> <{x := a'}>.
Proof.
  intros x a a' Heqv st st'.
  split; intros Hceval.
  - inversion Hceval. subst. apply E_Asgn. rewrite Heqv. reflexivity.
  - inversion Hceval. subst. apply E_Asgn. rewrite Heqv. reflexivity.
Qed.

Theorem CWhile_congruence : forall b b' c c',
  bequiv b b' -> cequiv c c' ->
  cequiv <{ while b do c end }> <{ while b' do c' end }>.
Proof.
  assert (A: forall (b b' : bexp) (c c' : com) (st st' : state),
      bequiv b b' -> cequiv c c' ->
      st =[ while b do c end ]=> st' ->
      st =[ while b' do c' end ]=> st').
  {
    unfold bequiv, cequiv.
    intros b b' c c' st st' Hbe Hc1e Hce.
    remember <{ while b do c end }> as cwhile eqn:Heqcwhile.
    induction Hce; inversion Heqcwhile; subst.
    + apply E_WhileFalse. rewrite <- Hbe. apply H.
    + apply E_WhileTrue with (st' := st').
      * rewrite <- Hbe. apply H.
      * apply Hc1e. apply Hce1.
      * apply IHHce2. reflexivity.
  }
  intros. split.
  - apply A; assumption.
  - apply A.
    + apply sym_bequiv. assumption.
    + apply sym_cequiv. assumption.
Qed.

Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv <{ c1;c2 }> <{ c1';c2' }>.
Proof.
  intros c1 c1' c2 c2' Hce1 Hce2 st st'.
  split; intros H; inversion H; subst.
  - apply E_Seq with st'0.
    + apply Hce1. apply H2.
    + apply Hce2. apply H5.
  - apply E_Seq with st'0.
    + apply Hce1. apply H2.
    + apply Hce2. apply H5.
Qed.

Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv <{ if b then c1 else c2 end }>
         <{ if b' then c1' else c2' end }>.
Proof.
  intros b b' c1 c1' c2 c2' Hbe Hce1 Hce2 st st'.
  split; intros H; inversion H; subst.
  - apply E_IfTrue.
    * rewrite <- H5. apply sym_bequiv. assumption.
    * unfold cequiv in Hce1. apply Hce1. assumption.
  - apply E_IfFalse.
    * unfold bequiv in Hbe. rewrite <- Hbe. assumption.
    * unfold cequiv in Hce2. apply Hce2. assumption.
  - apply E_IfTrue.
    * unfold bequiv in Hbe. rewrite Hbe. assumption.
    * unfold cequiv in Hce1. apply Hce1. assumption.
  - apply E_IfFalse.
    * unfold bequiv in Hbe. rewrite Hbe. assumption.
    * unfold cequiv in Hce2. apply Hce2. assumption.
Qed.

Example congruence_example:
  cequiv
    (* Program 1: *)
    <{ X := 0;
       if (X = 0) then Y := 0
       else Y := 42 end }>
    (* Program 2: *)
    <{ X := 0;
       if (X = 0) then Y := X - X (* <--- Changed here *)
       else Y := 42 end }>.
Proof.
  apply CSeq_congruence.
  - apply refl_cequiv.
  - apply CIf_congruence.
    + apply refl_bequiv.
    + apply CAsgn_congruence. unfold aequiv. simpl.
      symmetry. apply minus_diag.
    + apply refl_cequiv.
Qed.

Definition atrans_sound (atrans : aexp -> aexp) : Prop :=
  forall (a : aexp),
    aequiv a (atrans a).
Definition btrans_sound (btrans : bexp -> bexp) : Prop :=
  forall (b : bexp),
    bequiv b (btrans b).
Definition ctrans_sound (ctrans : com -> com) : Prop :=
  forall (c : com),
    cequiv c (ctrans c).

Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId x => AId x
  | <{ a1 + a2 }> =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 + n2)
    | (a1', a2') => <{ a1' + a2' }>
    end
  | <{ a1 - a2 }> =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 - n2)
    | (a1', a2') => <{ a1' - a2' }>
    end
  | <{ a1 * a2 }> =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 * n2)
    | (a1', a2') => <{ a1' * a2' }>
    end
  end.
Example fold_aexp_ex1 :
    fold_constants_aexp <{ (1 + 2) * X }>
  = <{ 3 * X }>.
Proof. reflexivity. Qed.

Example fold_aexp_ex2 :
  fold_constants_aexp <{ X - ((0 * 6) + Y) }> = <{ X - (0 + Y) }>.
Proof. reflexivity. Qed.

Fixpoint fold_constants_bexp (b : bexp) : bexp :=
  match b with
  | <{true}> => <{true}>
  | <{false}> => <{false}>
  | <{ a1 = a2 }> =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 =? n2 then <{true}> else <{false}>
      | (a1', a2') =>
          <{ a1' = a2' }>
      end
  | <{ a1 <> a2 }> =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if negb (n1 =? n2) then <{true}> else <{false}>
      | (a1', a2') =>
          <{ a1' <> a2' }>
      end
  | <{ a1 <= a2 }> =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 <=? n2 then <{true}> else <{false}>
      | (a1', a2') =>
          <{ a1' <= a2' }>
      end
  | <{ a1 > a2 }> =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 <=? n2 then <{false}> else <{true}>
      | (a1', a2') =>
          <{ a1' > a2' }>
      end
  | <{ ~ b1 }> =>
      match (fold_constants_bexp b1) with
      | <{true}> => <{false}>
      | <{false}> => <{true}>
      | b1' => <{ ~ b1' }>
      end
  | <{ b1 && b2 }> =>
      match (fold_constants_bexp b1,
             fold_constants_bexp b2) with
      | (<{true}>, <{true}>) => <{true}>
      | (<{true}>, <{false}>) => <{false}>
      | (<{false}>, <{true}>) => <{false}>
      | (<{false}>, <{false}>) => <{false}>
      | (b1', b2') => <{ b1' && b2' }>
      end
  end.
  
Example fold_bexp_ex1 :
  fold_constants_bexp <{ true && ~(false && true) }>
  = <{ true }>.
Proof. reflexivity. Qed.

Example fold_bexp_ex2 :
  fold_constants_bexp <{ (X = Y) && (0 = (2 - (1 + 1))) }>
  = <{ (X = Y) && true }>.
Proof. reflexivity. Qed.

Fixpoint fold_constants_com (c : com) : com :=
  match c with
  | <{ skip }> =>
      <{ skip }>
  | <{ x := a }> =>
      <{ x := (fold_constants_aexp a) }>
  | <{ c1 ; c2 }> =>
      <{ fold_constants_com c1 ; fold_constants_com c2 }>
  | <{ if b then c1 else c2 end }> =>
      match fold_constants_bexp b with
      | <{true}> => fold_constants_com c1
      | <{false}> => fold_constants_com c2
      | b' => <{ if b' then fold_constants_com c1
                       else fold_constants_com c2 end}>
      end
  | <{ while b do c1 end }> =>
      match fold_constants_bexp b with
      | <{true}> => <{ while true do skip end }>
      | <{false}> => <{ skip }>
      | b' => <{ while b' do (fold_constants_com c1) end }>
      end
  end.
Example fold_com_ex1 :
  fold_constants_com
    (* Original program: *)
    <{ X := 4 + 5;
       Y := X - 3;
       if ((X - Y) = (2 + 4)) then skip
       else Y := 0 end;
       if (0 <= (4 - (2 + 1))) then Y := 0
       else skip end;
       while (Y = 0) do
         X := X + 1
       end }>
  = (* After constant folding: *)
    <{ X := 9;
       Y := X - 3;
       if ((X - Y) = 6) then skip
       else Y := 0 end;
       Y := 0;
       while (Y = 0) do
         X := X + 1
       end }>.
Proof. reflexivity. Qed.

Theorem fold_constants_aexp_sound :
  atrans_sound fold_constants_aexp.
Proof.
  unfold atrans_sound. intros a. unfold aequiv. intros st.
  induction a; simpl; try reflexivity;
  try (
    destruct (fold_constants_aexp a1);
    destruct (fold_constants_aexp a2);
    rewrite IHa1; rewrite IHa2; reflexivity
  ).
Qed.

Theorem fold_constants_bexp_sound:
  btrans_sound fold_constants_bexp.
Proof.
  unfold btrans_sound. intros b. unfold bequiv. intros st.
  induction b;
    (* true and false are immediate *)
    try reflexivity.
  - (* BEq *)
    simpl.
    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1') by
       (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
       (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
    (* The only interesting case is when both a1 and a2
       become constants after folding *)
      simpl. destruct (n =? n0); reflexivity.
  - (* BNeq *)
    simpl.
    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1') by
       (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
       (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
    (* The only interesting case is when both a1 and a2
       become constants after folding *)
      simpl. destruct (n =? n0); reflexivity.
  - (* BLe *)
    simpl.
    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1') by
       (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
       (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
    (* The only interesting case is when both a1 and a2
       become constants after folding *)
      simpl. destruct (n <=? n0); reflexivity.
  - (* BGt *)
    simpl.
    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1') by
       (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
       (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
    (* The only interesting case is when both a1 and a2
       become constants after folding *)
      simpl. destruct (n <=? n0); reflexivity.
  - (* BNot *)
    simpl. remember (fold_constants_bexp b) as b' eqn:Heqb'.
    rewrite IHb.
    destruct b'; reflexivity.
  - (* BAnd *)
    simpl.
    remember (fold_constants_bexp b1) as b1' eqn:Heqb1'.
    remember (fold_constants_bexp b2) as b2' eqn:Heqb2'.
    rewrite IHb1. rewrite IHb2.
    destruct b1'; destruct b2'; reflexivity.
Qed.

Theorem fold_constants_com_sound :
  ctrans_sound fold_constants_com.
Proof.
  unfold ctrans_sound. intros c.
  induction c; simpl.
  - (* skip *) apply refl_cequiv.
  - (* := *) apply CAsgn_congruence.
              apply fold_constants_aexp_sound.
  - (* ; *) apply CSeq_congruence; assumption.
  - (* if *)
    assert (bequiv b (fold_constants_bexp b)). {
      apply fold_constants_bexp_sound. }
    destruct (fold_constants_bexp b) eqn:Heqb;
      try (apply CIf_congruence; assumption).
      (* (If the optimization doesn't eliminate the if, then the
          result is easy to prove from the IH and
          fold_constants_bexp_sound.) *)
    + (* b always true *)
      apply trans_cequiv with c1; try assumption.
      apply if_true; assumption.
    + (* b always false *)
      apply trans_cequiv with c2; try assumption.
      apply if_false; assumption.
  - assert (bequiv b (fold_constants_bexp b)). {
    apply fold_constants_bexp_sound. }
    destruct (fold_constants_bexp b) eqn:Heqb;
    try (apply CWhile_congruence; assumption).
    + apply while_true. assumption.
    + apply while_false. assumption.
Qed.

Fixpoint optimize_0plus_aexp (a : aexp) : aexp :=
  match a with
  | AId x => AId x
  | ANum n => ANum n
  | <{ 0 + a2 }> => optimize_0plus_aexp a2
  | <{ a1 + a2 }> => <{ (optimize_0plus_aexp a1) + (optimize_0plus_aexp a2) }>
  | <{ a1 - a2 }> => <{ (optimize_0plus_aexp a1) - (optimize_0plus_aexp a2) }>
  | <{ a1 * a2 }> => <{ (optimize_0plus_aexp a1) * (optimize_0plus_aexp a2) }>
  end.

Fixpoint optimize_0plus_bexp (b : bexp) : bexp :=
  match b with
  | <{ a1 = a2 }> => <{ (optimize_0plus_aexp a1) = (optimize_0plus_aexp a2) }>
  | <{ a1 <> a2 }> => <{ (optimize_0plus_aexp a1) <> (optimize_0plus_aexp a2) }>
  | <{ a1 <= a2 }> => <{ (optimize_0plus_aexp a1) <= (optimize_0plus_aexp a2) }>
  | <{ a1 > a2 }> => <{ (optimize_0plus_aexp a1) > (optimize_0plus_aexp a2) }>
  | <{ ~ b1 }> => <{ ~ (optimize_0plus_bexp b1) }>
  | _ => b
  end.
Fixpoint optimize_0plus_com (c : com) : com :=
  match c with
  | <{ skip }> =>
      <{ skip }>
  | <{ x := a }> =>
      <{ x := (optimize_0plus_aexp a) }>
  | <{ c1 ; c2 }> =>
      <{ optimize_0plus_com c1 ; optimize_0plus_com c2 }>
  | <{ if b then c1 else c2 end }> =>
      match optimize_0plus_bexp b with
      | <{true}> => optimize_0plus_com c1
      | <{false}> => optimize_0plus_com c2
      | b' => <{ if b' then optimize_0plus_com c1
                       else optimize_0plus_com c2 end}>
      end
  | <{ while b do c1 end }> =>
      match optimize_0plus_bexp b with
      | <{true}> => <{ while true do skip end }>
      | <{false}> => <{ skip }>
      | b' => <{ while b' do (optimize_0plus_com c1) end }>
      end
  end.
Example test_optimize_0plus:
    optimize_0plus_com
       <{ while X <> 0 do X := 0 + X - 1 end }>
  = <{ while X <> 0 do X := X - 1 end }>.
Proof.
  simpl. reflexivity.
Qed.

Theorem optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.
Proof.
  unfold atrans_sound, aequiv. intros.
  induction a; try (simpl; reflexivity).
  - destruct a1.
    + destruct n.
      * simpl. apply IHa2.
      * simpl. rewrite IHa2. reflexivity.
    + simpl. rewrite IHa2. reflexivity.
    + simpl. simpl in IHa1. rewrite IHa1. rewrite IHa2. reflexivity.
    + simpl. simpl in IHa1. rewrite IHa1. rewrite IHa2. reflexivity.
    + simpl. simpl in IHa1. rewrite IHa1. rewrite IHa2. reflexivity.
  - simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - simpl. rewrite IHa1. rewrite IHa2. reflexivity.
Qed.

Theorem optimize_0plus_bexp_sound :
  btrans_sound optimize_0plus_bexp.
Proof.
  unfold btrans_sound, bequiv. intros.
  induction b; try (simpl; reflexivity).
  - simpl.
    remember (optimize_0plus_aexp a1) as a1' eqn:Heqa1'.
    remember (optimize_0plus_aexp a2) as a2' eqn:Heqa2'.
Admitted.

Theorem optimize_0plus_com_sound :
  ctrans_sound optimize_0plus_com.
Proof.
  (* FILL IN HERE *) Admitted.
  
  Definition optimizer (c : com) := optimize_0plus_com (fold_constants_com c).
  
Theorem optimizer_sound :
  ctrans_sound optimizer.
Proof.
  unfold ctrans_sound, optimizer; intros.
  apply trans_cequiv with (fold_constants_com c).
  - apply fold_constants_com_sound.
  - apply (optimize_0plus_com_sound (fold_constants_com c)).
  

