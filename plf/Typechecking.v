Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
Set Warnings "-non-recursive".
From Coq Require Import Bool.Bool.
From PLF Require Import Maps.
From PLF Require Import Smallstep.
From PLF Require Import Stlc.
From PLF Require MoreStlc.
Module STLCTypes.
Export STLC.

Fixpoint eqb_ty (T1 T2:ty) : bool :=
  match T1,T2 with
  | <{ Bool }> , <{ Bool }> =>
      true
  | <{ T11->T12 }>, <{ T21->T22 }> =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | _,_ =>
      false
  end.
  
Lemma eqb_ty_refl : forall T,
  eqb_ty T T = true.
Proof.
  intros T. induction T; simpl.
    reflexivity.
    rewrite IHT1. rewrite IHT2. reflexivity. Qed.

Lemma eqb_ty__eq : forall T1 T2,
  eqb_ty T1 T2 = true -> T1 = T2.
Proof with auto.
  intros T1. induction T1; intros T2 Hbeq; destruct T2; inversion Hbeq.
  - (* T1=Bool *)
    reflexivity.
  - (* T1 = T1_1->T1_2 *)
    rewrite andb_true_iff in H0. inversion H0 as [Hbeq1 Hbeq2].
    apply IHT1_1 in Hbeq1. apply IHT1_2 in Hbeq2. subst... Qed.
End STLCTypes.

Module FirstTry.
Import STLCTypes.
Fixpoint type_check (Gamma : context) (t : tm) : option ty :=
  match t with
  | tm_var x =>
      Gamma x
  | <{\x:T2, t1}> =>
      match type_check (x |-> T2 ; Gamma) t1 with
      | Some T1 => Some <{T2->T1}>
      | _ => None
      end
  | <{t1 t2}> =>
      match type_check Gamma t1, type_check Gamma t2 with
      | Some <{T11->T12}>, Some T2 =>
          if eqb_ty T11 T2 then Some T12 else None
      | _,_ => None
      end
  | <{true}> =>
      Some <{Bool}>
  | <{false}> =>
      Some <{Bool}>
  | <{if guard then t else f}> =>
      match type_check Gamma guard with
      | Some <{Bool}> =>
          match type_check Gamma t, type_check Gamma f with
          | Some T1, Some T2 =>
              if eqb_ty T1 T2 then Some T1 else None
          | _,_ => None
          end
      | _ => None
      end
  end.
End FirstTry.


Notation " x <- e1 ;; e2" := (match e1 with
                              | Some x => e2
                              | None => None
                              end)
         (right associativity, at level 60).

Notation " 'return' e " := (Some e) (at level 60).
Notation " 'fail' " := None.

Module STLCChecker.
Import STLCTypes.

Fixpoint type_check (Gamma : context) (t : tm) : option ty :=
  match t with
  | tm_var x =>
      match Gamma x with
      | Some T => return T
      | None => fail
      end
  | <{\x:T2, t1}> =>
      T1 <- type_check (x |-> T2 ; Gamma) t1 ;;
      return <{T2->T1}>
  | <{t1 t2}> =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1 with
      | <{T11->T12}> =>
          if eqb_ty T11 T2 then return T12 else fail
      | _ => fail
      end
  | <{true}> =>
      return <{ Bool }>
  | <{false}> =>
      return <{ Bool }>
  | <{if guard then t1 else t2}> =>
      Tguard <- type_check Gamma guard ;;
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match Tguard with
      | <{ Bool }> =>
          if eqb_ty T1 T2 then return T1 else fail
      | _ => fail
      end
  end.
  
Theorem type_checking_sound : forall Gamma t T,
  type_check Gamma t = Some T -> has_type Gamma t T.
Proof with eauto.
  intros Gamma t. generalize dependent Gamma.
  induction t; intros Gamma T Htc; inversion Htc.
  - (* var *) rename s into x. destruct (Gamma x) eqn:H.
    rename t into T'. inversion H0. subst. eauto. solve_by_invert.
  - (* app *)
    remember (type_check Gamma t1) as TO1.
    destruct TO1 as [T1|]; try solve_by_invert;
    destruct T1 as [|T11 T12]; try solve_by_invert;
    remember (type_check Gamma t2) as TO2;
    destruct TO2 as [T2|]; try solve_by_invert.
    destruct (eqb_ty T11 T2) eqn: Heqb.
    apply eqb_ty__eq in Heqb.
    inversion H0; subst...
    inversion H0.
  - (* abs *)
    rename s into x, t into T1.
    remember (x |-> T1 ; Gamma) as G'.
    remember (type_check G' t0) as TO2.
    destruct TO2; try solve_by_invert.
    inversion H0; subst...
  - (* tru *) eauto.
  - (* fls *) eauto.
  - (* test *)
    remember (type_check Gamma t1) as TOc.
    remember (type_check Gamma t2) as TO1.
    remember (type_check Gamma t3) as TO2.
    destruct TOc as [Tc|]; try solve_by_invert.
    destruct Tc; try solve_by_invert;
    destruct TO1 as [T1|]; try solve_by_invert;
    destruct TO2 as [T2|]; try solve_by_invert.
    destruct (eqb_ty T1 T2) eqn:Heqb;
    try solve_by_invert.
    apply eqb_ty__eq in Heqb.
    inversion H0. subst. subst...
Qed.

Theorem type_checking_complete : forall Gamma t T,
  has_type Gamma t T -> type_check Gamma t = Some T.
Proof with auto.
  intros Gamma t T Hty.
  induction Hty; simpl.
  - (* T_Var *) destruct (Gamma _) eqn:H0; assumption.
  - (* T_Abs *) rewrite IHHty...
  - (* T_App *)
    rewrite IHHty1. rewrite IHHty2.
    rewrite (eqb_ty_refl T2)...
  - (* T_True *) eauto.
  - (* T_False *) eauto.
  - (* T_If *) rewrite IHHty1. rewrite IHHty2.
    rewrite IHHty3. rewrite (eqb_ty_refl T1)...
Qed.

End STLCChecker.

Module TypecheckerExtensions.
Import MoreStlc.
Import STLCExtended.
Fixpoint eqb_ty (T1 T2 : ty) : bool :=
  match T1,T2 with
  | <{{Nat}}>, <{{Nat}}> =>
      true
  | <{{Unit}}>, <{{Unit}}> =>
      true
  | <{{T11 -> T12}}>, <{{T21 -> T22}}> =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | <{{T11 * T12}}>, <{{T21 * T22}}> =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | <{{T11 + T12}}>, <{{T21 + T22}}> =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | <{{List T11}}>, <{{List T21}}> =>
      eqb_ty T11 T21
  | _,_ =>
      false
  end.
  

Lemma eqb_ty_refl : forall T,
  eqb_ty T T = true.
Proof.
  intros T.
  induction T; simpl; auto;
    rewrite IHT1; rewrite IHT2; reflexivity. Qed.

Lemma eqb_ty__eq : forall T1 T2,
  eqb_ty T1 T2 = true -> T1 = T2.
Proof.
  intros T1.
  induction T1; intros T2 Hbeq; destruct T2; inversion Hbeq;
    try reflexivity;
    try (rewrite andb_true_iff in H0; inversion H0 as [Hbeq1 Hbeq2];
         apply IHT1_1 in Hbeq1; apply IHT1_2 in Hbeq2; subst; auto);
    try (apply IHT1 in Hbeq; subst; auto).
 Qed.

Fixpoint type_check (Gamma : context) (t : tm) : option ty :=
  match t with
  | tm_var x =>
      match Gamma x with
      | Some T => return T
      | None => fail
      end
  | <{ \ x1 : T1, t2 }> =>
      T2 <- type_check (x1 |-> T1 ; Gamma) t2 ;;
      return <{{T1 -> T2}}>
  | <{ t1 t2 }> =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1 with
      | <{{T11 -> T12}}> =>
          if eqb_ty T11 T2 then return T12 else fail
      | _ => fail
      end
  | tm_const _ =>
      return <{{Nat}}>
  | <{ succ t1 }> =>
      T1 <- type_check Gamma t1 ;;
      match T1 with
      | <{{Nat}}> => return <{{Nat}}>
      | _ => fail
      end
  | <{ pred t1 }> =>
      T1 <- type_check Gamma t1 ;;
      match T1 with
      | <{{Nat}}> => return <{{Nat}}>
      | _ => fail
      end
  | <{ t1 * t2 }> =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1, T2 with
      | <{{Nat}}>, <{{Nat}}> => return <{{Nat}}>
      | _,_ => fail
      end
  | <{ if0 guard then t else f }> =>
      Tguard <- type_check Gamma guard ;;
      T1 <- type_check Gamma t ;;
      T2 <- type_check Gamma f ;;
      match Tguard with
      | <{{Nat}}> => if eqb_ty T1 T2 then return T1 else fail
      | _ => fail
      end

  (* Complete the following cases. *)
  
  (* sums *)
  | <{ inl T2 t }> =>
    T1 <- type_check Gamma t ;;
    return <{{ T1 + T2 }}>
  | <{ inr T1 t }> =>
    T2 <- type_check Gamma t ;;
    return <{{ T1 + T2 }}>
  | <{case t of | inl x1 => t1 | inr x2 => t2}> =>
      match type_check Gamma t with
      | Some <{{ T1 + T2 }}> => 
        TR1 <- type_check (x1 |-> T1; Gamma) t1 ;;
        TR2 <- type_check (x2 |-> T2; Gamma) t2 ;;
        if eqb_ty TR1 TR2 then return TR1 else fail
      | _ => fail
      end
  (* lists (the tm_lcase is given for free) *)
  | <{ nil T }> => return <{{ List T }}>
  | <{ h :: t }> =>
    Th <- type_check Gamma h ;;
    match type_check Gamma t with
    | Some <{{ List T }}> => if eqb_ty T Th then return <{{ List T }}> else fail
    | _ => fail
    end
  | <{ case t0 of | nil => t1 | x21 :: x22 => t2 }> =>
      T0 <- type_check Gamma t0 ;;
      match T0 with
      | <{{List T}}> =>
          T1 <- type_check Gamma t1 ;;
          T2 <- type_check (x21 |-> T ; x22 |-> <{{List T}}> ; Gamma) t2 ;;
          if eqb_ty T1 T2 then return T1 else fail
      | _ => fail
      end
  (* unit *)
  | <{ unit }> => return <{{ Unit }}>
  (* pairs *)
  | <{ (t1, t2) }> =>
    T1 <- type_check Gamma t1 ;;
    T2 <- type_check Gamma t2 ;;
    return <{{ (T1*T2) }}>
  (* let *)
  | <{let x = v in t}> => 
    T <- type_check Gamma v ;;
    type_check (x |-> T; Gamma) t
  (* fix *)
  | <{ fix t }> => 
    match type_check Gamma t with
    | Some <{{ T -> T' }}> => if eqb_ty T T' then return T else fail
    | _ => fail
    end
  | _ => None (* ... and delete this line when you complete the exercise. *)
  end.
(* Do not modify the following line: *)
Definition manual_grade_for_type_check_defn : option (nat*string) := None. 

Ltac invert_typecheck Gamma t T :=
  remember (type_check Gamma t) as TO;
  destruct TO as [T|];
  try solve_by_invert; try (inversion H0; eauto); try (subst; eauto).
Ltac analyze T T1 T2 :=
  destruct T as [T1 T2| |T1 T2|T1| |T1 T2]; try solve_by_invert.
Ltac fully_invert_typecheck Gamma t T T1 T2 :=
  let TX := fresh T in
  remember (type_check Gamma t) as TO;
  destruct TO as [TX|]; try solve_by_invert;
  destruct TX as [T1 T2| |T1 T2|T1| |T1 T2];
  try solve_by_invert; try (inversion H0; eauto); try (subst; eauto).
Ltac case_equality S T :=
  destruct (eqb_ty S T) eqn: Heqb;
  inversion H0; apply eqb_ty__eq in Heqb; subst; subst; eauto.
  
Theorem type_checking_sound : forall Gamma t T,
  type_check Gamma t = Some T ->
  has_type Gamma t T.
Proof with eauto.
  intros Gamma t. generalize dependent Gamma.
  induction t; intros Gamma T Htc; inversion Htc.
  - (* var *) rename s into x. destruct (Gamma x) eqn:H.
    rename t into T'. inversion H0. subst. eauto. solve_by_invert.
  - (* app *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    analyze T1 T11 T12.
    case_equality T11 T2.
  - (* abs *)
    rename s into x, t into T1.
    remember (x |-> T1 ; Gamma) as Gamma'.
    invert_typecheck Gamma' t0 T0.
  - (* const *) eauto.
  - (* scc *)
    rename t into t1.
    fully_invert_typecheck Gamma t1 T1 T11 T12.
  - (* prd *)
    rename t into t1.
    fully_invert_typecheck Gamma t1 T1 T11 T12.
  - (* mlt *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    analyze T1 T11 T12; analyze T2 T21 T22.
    inversion H0. subst. eauto.
  - (* test0 *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    invert_typecheck Gamma t3 T3.
    destruct T1; try solve_by_invert.
    case_equality T2 T3.
  (* Complete the following cases. *)
  (* sums *)
  - (* inl *)
  rename t into T2.
  invert_typecheck Gamma t0 T1.
  - (* inr *)
    rename t into T1.
    invert_typecheck Gamma t0 T2.
  - (* sum case *)
    invert_typecheck Gamma t1 T12.
    analyze T12 T1 T2.
    rename s into x1. rename s0 into x2.
    rename t1 into t0. rename t2 into t1. rename t3 into t2.
    invert_typecheck (x1 |-> T1; Gamma) t1 HT3.
    invert_typecheck (x2 |-> T2; Gamma) t2 HT3'.
    case_equality HT3 HT3'.
  (* lists (the tm_lcase is given for free) *)
  (* nil *)
  - eauto.
  - (* cons *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    analyze T2 T2' T2''.
    case_equality T2' T1.  
  (* FILL IN HERE *)
  - (* tlcase *)
    rename s into x31, s0 into x32.
    fully_invert_typecheck Gamma t1 T1 T11 T12.
    invert_typecheck Gamma t2 T2.
    remember (x31 |-> T11 ; x32 |-> <{{List T11}}> ; Gamma) as Gamma'2.
    invert_typecheck Gamma'2 t3 T3.
    case_equality T2 T3.
  - (* unit *)
    eauto.
  (* pairs *)
  - (* pair *)
  invert_typecheck Gamma t1 T1.
  invert_typecheck Gamma t2 T2.
  - (* fst *)
    (* invert_typecheck Gamma t T'.
    analyze T' T'1 T'2.
    inversion H0. subst. eauto. *)
  - (* snd *)
    (* invert_typecheck Gamma t T'.
    analyze T' T'1 T'2.
    inversion H0. subst. eauto. *)
  - (* let *)
    (* invert_typecheck Gamma t1 T'. *)
  - (* fix *)
    (* invert_typecheck Gamma t T'.
    analyze T' T'1 T'2.
    case_equality T'1 T'2. *)
Admitted.

Theorem type_checking_complete : forall Gamma t T,
  has_type Gamma t T ->
  type_check Gamma t = Some T.
Proof.
  intros Gamma t T Hty.
  induction Hty; simpl;
    try (rewrite IHHty);
    try (rewrite IHHty1);
    try (rewrite IHHty2);
    try (rewrite IHHty3);
    try (rewrite (eqb_ty_refl T0));
    try (rewrite (eqb_ty_refl T1));
    try (rewrite (eqb_ty_refl T2));
    try (rewrite (eqb_ty_refl T3));
    eauto.
    - destruct (Gamma _); [assumption| solve_by_invert].
  (* The above proof script suffices for the reference solution. *)
  (* FILL IN HERE *) Admitted.

End TypecheckerExtensions.

Module StepFunction.
Import MoreStlc.
Import STLCExtended.

(* We must first also redefine value as a function. *)
Fixpoint valuef (t : tm) : bool :=
  match t with
  | tm_var _ => false
  | <{ \_:_, _ }> => true
  | <{ _ _ }> => false
  | tm_const _ => true
  | <{ succ _ }> | <{ pred _ }> | <{ _ * _ }> | <{ if0 _ then _ else _ }> => false
  (* Complete the following cases *)
  (* sums *)
  | <{ (t1, t2) }> => (valuef t1) && (valuef t2)
  | <{ t1.fst }> => false
  | <{ t1.snd }> => false
  | <{ let _ = _ in _ }> => false
  | <{inl _ t1}> => valuef t1
  | <{inr _ t1}> => valuef t1
  | <{ case _ of | inl _ => _ | inr _ => _ }> => false
  | <{ nil _ }> => true
  | <{ x :: xs }> => (valuef x) && (valuef xs)
  | <{ case _ of | nil => _ | _ :: _ => _ }> => false
  | <{ unit }> => true
  | <{ fix _ }> => false
  (* | _ => false  *)
  (* ... and delete this line when you complete the exercise. *)
  end.
(* Do not modify the following line: *)
Definition manual_grade_for_valuef_defn : option (nat*string) := None.

(* A little helper to concisely check some boolean properties
   (in this case, that some term is a value, with valuef). *)
Definition assert (b : bool) (a : option tm) : option tm :=
  if b then a else None.
  
(* Operational semantics as a Coq function. *)
Fixpoint stepf (t : tm) : option tm :=
  match t with
  (* pure STLC *)
  | tm_var x => None (* We only define step for closed terms *)
  | <{ \x1:T1, t2 }> => None (* Abstraction is a value *)
  | <{ t1 t2 }> =>
    match stepf t1, stepf t2, t1 with
    | Some t1', _, _ => Some <{ t1' t2 }>
    (* otherwise t1 is a normal form *)
    | None, Some t2', _ => assert (valuef t1) (Some <{ t1 t2' }>)
    (* otherwise t1, t2 are normal forms *)
    | None, None, <{ \x:T, t11 }> =>
      assert (valuef t2) (Some <{ [x:=t2]t11 }>)
    | _, _, _ => None
    end
  (* numbers *)
  | tm_const _ => None (* number value *)
  | <{ succ t1 }> =>
    match stepf t1, t1 with
    | Some t1', _ => Some <{ succ t1' }>
    (* otherwise t1 is a normal form *)
    | None, tm_const n => Some (tm_const (S n))
    | None, _ => None
    end
  | <{ pred t1 }> =>
    match stepf t1, t1 with
    | Some t1', _ => Some <{ pred t1' }>
    (* otherwise t1 is a normal form *)
    | None, tm_const n => Some (tm_const (n - 1))
    | _, _ => None
    end
  | <{ t1 * t2 }> =>
    match stepf t1, stepf t2, t1, t2 with
    | Some t1', _, _, _ => Some <{ t1' * t2 }>
    (* otherwise t1 is a normal form *)
    | None, Some t2', _, _ =>
      assert (valuef t1) (Some <{ t1 * t2' }>)
    | None, None, tm_const n1, tm_const n2 => Some (tm_const (mult n1 n2))
    | _, _, _, _ => None
    end
  | <{ if0 guard then t else f }> =>
    match stepf guard, guard with
    | Some guard', _ => Some <{ if0 guard' then t else f }>
    (* otherwise guard is a normal form *)
    | None, tm_const 0 => Some t
    | None, tm_const (S _) => Some f
    | _, _ => None
    end
  (* Complete the following cases. *)
  (* sums *)
  | <{inl T2 t}> => match stepf t with
    | Some t' => assert (valuef t') (Some <{inl T2 t'}>)
    | _ => None
    end
  | <{inr T1 t}> => match stepf t with
    | Some t' => assert (valuef t') (Some <{inr T1 t'}>)
    | _ => None
    end
  | <{ case t of | inl x1 => t1 | inr x2 => t2 }> =>
    match stepf t with
    | Some t' => assert (valuef t') (Some <{ case t' of | inl x1 => t1 | inr x2 => t2 }>)
    | None => match t with
              | <{inl T2 t' }> => assert (valuef t') (Some <{ [x1:=t']t1 }>)
              | <{inr T1 t' }> => assert (valuef t') (Some <{ [x2:=t']t2 }>)
              | _ => None
              end
    end
  (* lists (the tm_lcase is given for free) *)
    | <{ nil _ }> => None
    | <{ x :: xs }> => 
      match stepf x, stepf xs, x, xs with
      | Some x', _, _, _ => assert (valuef x') (Some <{ x' :: xs }>)
      | None, Some xs', _, _ => assert ((valuef x) && (valuef xs')) (Some <{ x :: xs' }>)
      | _, _, _, _ => None
      end
    | <{ case t0 of | nil => t1 | x21 :: x22 => t2 }> =>
    match stepf t0, t0 with
    | Some t0', _ => Some <{ case t0' of | nil => t1 | x21 :: x22 => t2 }>
    (* otherwise t0 is a normal form *)
    | None, <{ nil _ }> => Some t1
    | None, <{ vh :: vt }> =>
      assert (valuef vh) (assert (valuef vt)
        (Some <{ [x22:=vt]([x21:=vh]t2) }> ))
    | None, _ => None
    end
  (* unit *)
    | <{ unit }> => None
  (* pairs *)
    | <{ (t1, t2) }> => 
    match stepf t1, stepf t2, t1, t2 with
    | Some t1', _, _, _ => Some <{ (t1', t2) }>
    | None, Some t2', _, _ => assert (valuef t1) (Some <{ (t1, t2') }>)
    | _, _, _, _ => None 
    end
    | <{ t.fst }> => 
    match stepf t, t with
    | Some t', _ => Some <{ t'.fst }>
    | None, <{ (t1, t2) }> => assert ((valuef t1) && (valuef t2)) (Some t1)
    | _, _ => None 
    end
    | <{ t.snd }> => 
    match stepf t, t with
    | Some t', _ => Some <{ t'.snd }>
    | None, <{ (t1, t2) }> => assert ((valuef t1) && (valuef t2)) (Some t2)
    | _, _ => None 
    end
  (* let *)
    | <{ let x = v in t }> => match stepf v with
      | Some v' => assert (valuef v') (Some <{ let x = v' in t }>)
      | None => assert (valuef v) (Some <{ [x:=v]t }>) 
      end
  (* fix *)
    | <{ fix t }> => match t with
      | <{ \xf:T, t }> => Some (<{ [xf:= fix (\xf:T, t)]t }>)
      | _ => match stepf t with
        | Some t' => (Some <{ fix t' }>)
        | _ => None
        end
      end
  end.
(* Do not modify the following line: *)
Definition manual_grade_for_stepf_defn : option (nat*string) := None.
(* To prove that stepf is equivalent to step, we start with
   a couple of intermediate lemmas. *)
(* We show that valuef is sound and complete with respect to value. *)

Lemma sound_valuef : forall t,
    valuef t = true -> value t.
Proof.
  (* FILL IN HERE *) Admitted.
  
  
(* valuef is complete with respect to value.
   This proof by induction is quite easily done by simplification. *)
   Lemma complete_valuef : forall t,
   value t -> valuef t = true.
Proof.
 (* FILL IN HERE *) Admitted.
(* Soundness of stepf:

  Theorem sound_stepf : forall t t',
      stepf t = Some t'  ->  t --> t'.

  By induction on t. We automate the handling of each case with
  the following tactic auto_stepf. *)
Tactic Notation "auto_stepf" ident(H) :=
 (* Step 1: In every case, the left hand side of the hypothesis
    H : stepf t = Some t' simplifies to some combination of
    match u with ... end, assert u (...) (for some u).
    The tactic auto_stepf then destructs u as required.
    We repeat this step as long as it is possible. *)
 repeat
   match type of H with
   | (match ?u with _ => _ end = _) =>
     let e := fresh "e" in
     destruct u eqn:e
   | (assert ?u _ = _) =>
     (* In this case, u is always of the form valuef t0
        for some term t0. If valuef t0 = true, we immediately
        deduce value t0 via sound_valuef. If valuef t0 = false,
        then that equation simplifies to None = Some t', which is
        contradictory and can be eliminated with discriminate. *)
     let e := fresh "e" in
     destruct u eqn:e;
     simpl in H; (* assert true (...) must be simplified
                    explicitly. *)
     [apply sound_valuef in e | discriminate]
   end;
 (* Step 2: We are now left with either H : None = Some t' or
    Some (...) = Some t', and the rest of the proof is a
    straightforward combination of the induction hypotheses. *)
 (discriminate + (inversion H; subst; auto)).
 
(* Soundness of stepf. *)
Theorem sound_stepf : forall t t',
    stepf t = Some t' -> t --> t'.
Proof.
  intros t.
  induction t; simpl; intros t' H;
    auto_stepf H.
 (* The above proof script suffices for the reference solution. *)
 (* FILL IN HERE *) Admitted.
 
(* Now for completeness, another lemma will be useful:
   every value is a normal form for stepf. *)
Lemma value_stepf_nf : forall t,
  value t -> stepf t = None.
Proof.
 (* FILL IN HERE *) Admitted.
 
(* Completeness of stepf. *)
Theorem complete_stepf : forall t t',
   t --> t' -> stepf t = Some t'.
Proof.
 (* FILL IN HERE *) Admitted.
End StepFunction.
Module StlcImpl.
Import StepFunction.
(* FILL IN HERE *)
End StlcImpl.

