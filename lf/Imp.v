Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From LF Require Import Maps.
Set Default Goal Selector "!".


Module AExp.

Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2: aexp)
  | AMinus (a1 a2: aexp)
  | AMult (a1 a2: aexp)
  .

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (a : bexp)
  | BAnd (a1 a2 : bexp)
  .

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.
  
Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. reflexivity. Qed.

Fixpoint beval(b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => (aeval a1) =? (aeval a2) 
  | BNeq a1 a2 => negb((aeval a1) =? (aeval a2))
  | BLe a1 a2 => (aeval a1) <=? (aeval a2) 
  | BGt a1 a2 => negb((aeval a1) <=? (aeval a2)) 
  | BNot b1 => negb (beval b1)
  | BAnd b1 b2 => andb (beval b1) (beval b2)
  end.

Fixpoint optimize_0plus (a: aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimize_0plus e2
  | APlus e1 e2 => APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 => AMult (optimize_0plus e1) (optimize_0plus e2)
  end.
  
Example test_optimize_0plus:
  optimize_0plus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1).
Proof. reflexivity. Qed.

Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a. induction a.
  - (* ANum *) reflexivity.
  - (* APlus *) destruct a1 eqn:Ea1.
    + (* a1 = ANum n *) destruct n eqn:En.
      * (* n = 0 *) simpl. apply IHa2.
      * (* n <> 0 *) simpl. rewrite IHa2. reflexivity.
    + (* a1 = APlus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMinus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMult a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
  - (* AMinus *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - (* AMult *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.
Qed.

Theorem silly1 : forall ae, aeval ae = aeval ae.
Proof.
    try reflexivity. (* This just does reflexivity. *)
Qed.

Theorem silly2 : forall (P : Prop), P -> P.
Proof.
  intros P HP.
  try reflexivity. (* Plain reflexivity would have failed. *)
  apply HP. (* We can still finish the proof in some other way. *)
Qed.

Lemma foo : forall n, 0 <=? n = true.
Proof.
  intros.
  destruct n.
    (* Leaves two subgoals, which are discharged identically...  *)
    - (* n=0 *) simpl. reflexivity.
    - (* n=Sn' *) simpl. reflexivity.
Qed.

Lemma foo' : forall n, 0 <=? n = true.
Proof.
  intros.
  (* destruct the current goal *)
  destruct n;
  (* then simpl each resulting subgoal *)
  simpl;
  (* and do reflexivity on each resulting subgoal *)
  reflexivity.
Qed.

Theorem optimize_0plus_sound': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* Most cases follow directly by the IH... *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
    (* ... but the remaining cases -- ANum and APlus --
       are different: *)
  - (* ANum *) reflexivity.
  - (* APlus *)
    destruct a1 eqn:Ea1;
      (* Again, most cases follow directly by the IH: *)
      try (simpl; simpl in IHa1; rewrite IHa1;
           rewrite IHa2; reflexivity).
    (* The interesting case, on which the try...
       does nothing, is when e1 = ANum n. In this
       case, we have to destruct n (to see whether
       the optimization applies) and rewrite with the
       induction hypothesis. *)
    + (* a1 = ANum n *) destruct n eqn:En;
      simpl; rewrite IHa2; reflexivity.
Qed.

Theorem optimize_0plus_sound'': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* Most cases follow directly by the IH *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    (* ... or are immediate by definition *)
    try reflexivity.
  (* The interesting case is when a = APlus a1 a2. *)
  - (* APlus *)
    destruct a1; try (simpl; simpl in IHa1; rewrite IHa1;
                      rewrite IHa2; reflexivity).
    + (* a1 = ANum n *) destruct n;
      simpl; rewrite IHa2; reflexivity.
Qed.

Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (try (left; reflexivity); right).
Qed.

Theorem In10' : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat simpl.
  repeat (left; reflexivity).
  repeat (right; try (left; reflexivity)).
Qed.

Theorem repeat_loop : forall (m n : nat),
  m + n = n + m.
Proof.
  intros m n.
  (* Uncomment the next line to see the infinite loop occur.  You will
     then need to interrupt Coq to make it listen to you again.  (In
     Proof General, C-c C-c does this.) *)
  (* repeat rewrite Nat.add_comm. *)
Admitted.

Fixpoint optimize_0plus_b (b : bexp) : bexp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 => BEq (optimize_0plus a1) (optimize_0plus a2) 
  | BNeq a1 a2 => BNeq (optimize_0plus a1) (optimize_0plus a2)
  | BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2) 
  | BGt a1 a2 => BGt (optimize_0plus a1) (optimize_0plus a2)
  | BNot b1 => BNot (optimize_0plus_b b1)
  | BAnd b1 b2 => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
  end.
  

Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
  intros b.
  induction b;
  try (simpl; repeat (rewrite optimize_0plus_sound); reflexivity ).
  - simpl. rewrite IHb. reflexivity.
  - simpl. rewrite IHb1. rewrite IHb2. reflexivity.
Qed.

Ltac invert H := inversion H; subst; clear H.

Lemma invert_example1: forall {a b c: nat}, [a ;b] = [a;c] -> b = c.
  intros.
  invert H.
  reflexivity.
Qed.

Example silly_presburger_example : forall m n o p,
  m + n <= n + o /\ o + 3 = p + 3 ->
  m <= p.
Proof.
  intros. lia.
Qed.

Example add_comm__lia : forall m n,
    m + n = n + m.
Proof.
  intros. lia.
Qed.
Example add_assoc__lia : forall m n p,
    m + (n + p) = m + n + p.
Proof.
  intros. lia.
Qed.

Module aevalR_first_try.

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      aevalR (ANum n) n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMult e1 e2) (n1 * n2).

Module HypothesisNames.

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      aevalR (ANum n) n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (AMult e1 e2) (n1 * n2).
End HypothesisNames.

Notation "e '==>' n"
         := (aevalR e n)
            (at level 90, left associativity)
         : type_scope.
End aevalR_first_try.

Reserved Notation "e '==>' n" (at level 90, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (APlus e1 e2) ==> (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (AMinus e1 e2) ==> (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (AMult e1 e2) ==> (n1 * n2)

  where "e '==>' n" := (aevalR e n) : type_scope.

Reserved Notation "e '==>b' b" (at level 90, left associativity).

Inductive bevalR : bexp -> bool -> Prop :=
  | E_BTrue : bevalR BTrue true
  | E_BFalse : bevalR BFalse false
  | E_BEq (a1 a2 : aexp) (n1 n2 : nat): 
    aevalR a1 n1 ->
    aevalR a2 n2 ->
    bevalR (BEq a1 a2) (n1 =? n2)
  | E_BNeq (a1 a2 : aexp) (n1 n2 : nat): 
    aevalR a1 n1 ->
    aevalR a2 n2 ->
    bevalR (BNeq a1 a2) (negb (n1 =? n2))
  | E_BLe (a1 a2 : aexp) (n1 n2 : nat): 
    aevalR a1 n1 ->
    aevalR a2 n2 ->
    bevalR (BLe a1 a2) (n1 <=? n2)
  | E_BGt (a1 a2 : aexp) (n1 n2 : nat): 
    aevalR a1 n1 ->
    aevalR a2 n2 ->
    bevalR (BGt a1 a2) (negb (n1 <=? n2))
  | E_BNot (a : bexp) (b : bool): 
    bevalR a b ->
    bevalR (BNot a) (negb b)
  | E_BAnd (a1 a2: bexp ) (b1 b2 : bool): 
    bevalR a1 b1 ->
    bevalR a2 b2 ->
    bevalR (BAnd a1 a2) (andb b1 b2)

where "e '==>b' b" := (bevalR e b) : type_scope.

Theorem aeval_iff_aevalR : forall a n,
  (a ==> n) <-> aeval a = n.
Proof.
 split.
 - (* -> *)
   intros H.
   induction H; simpl.
   + (* E_ANum *)
     reflexivity.
   + (* E_APlus *)
     rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
   + (* E_AMinus *)
     rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
   + (* E_AMult *)
     rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
 - (* <- *)
   generalize dependent n.
   induction a;
      simpl; intros; subst.
   + (* ANum *)
     apply E_ANum.
   + (* APlus *)
     apply E_APlus.
     * apply IHa1. reflexivity.
     * apply IHa2. reflexivity.
   + (* AMinus *)
     apply E_AMinus.
     * apply IHa1. reflexivity.
     * apply IHa2. reflexivity.
   + (* AMult *)
     apply E_AMult.
     * apply IHa1. reflexivity.
     * apply IHa2. reflexivity.
Qed.

Theorem aeval_iff_aevalR' : forall a n,
  (a ==> n) <-> aeval a = n.
Proof.
  (* WORKED IN CLASS *)
  split.
  - (* -> *)
    intros H; induction H; subst; reflexivity.
  - (* <- *)
    generalize dependent n.
    induction a; simpl; intros; subst; constructor;
       try apply IHa1; try apply IHa2; reflexivity.
Qed.

Lemma beval_iff_bevalR : forall b bv,
  b ==>b bv <-> beval b = bv.
Proof.
  split.
  - intros H; induction H; simpl; subst;
     try apply aeval_iff_aevalR in H; try apply aeval_iff_aevalR in H0; try rewrite H0; try rewrite H; try reflexivity.
  - intros; destruct b; simpl; subst; constructor;
    try (apply aeval_iff_aevalR; reflexivity);
    [ | rename b1 into b | rename b2 into b ];
    induction b; constructor;
    try (apply aeval_iff_aevalR; reflexivity);
    try (apply IHb);
    try (apply IHb1);
    try (apply IHb2).
Qed.
End AExp.

Module aevalR_division.

Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ADiv (a1 a2 : aexp). (* <--- NEW *)
  
Reserved Notation "e '==>' n"
  (at level 90, left associativity).
Inductive aevalR : aexp -> nat -> Prop :=
| E_ANum (n : nat) :
  (ANum n) ==> n
| E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
  (a1 ==> n1) -> (a2 ==> n2) -> (APlus a1 a2) ==> (n1 + n2)
| E_AMinus (a1 a2 : aexp) (n1 n2 : nat) :
  (a1 ==> n1) -> (a2 ==> n2) -> (AMinus a1 a2) ==> (n1 - n2)
| E_AMult (a1 a2 : aexp) (n1 n2 : nat) :
  (a1 ==> n1) -> (a2 ==> n2) -> (AMult a1 a2) ==> (n1 * n2)
| E_ADiv (a1 a2 : aexp) (n1 n2 n3 : nat) : (* <----- NEW *)
  (a1 ==> n1) -> (a2 ==> n2) -> (n2 > 0) ->
(mult n2 n3 = n1) -> (ADiv a1 a2) ==> n3

where "a '==>' n" := (aevalR a n) : type_scope.

End aevalR_division.
Module aevalR_extended.

Reserved Notation "e '==>' n" (at level 90, left associativity).
Inductive aexp : Type :=
  | AAny (* <--- NEW *)
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive aevalR : aexp -> nat -> Prop :=
| E_Any (n : nat) :
    AAny ==> n (* <--- NEW *)
| E_ANum (n : nat) :
    (ANum n) ==> n
| E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
    (a1 ==> n1) -> (a2 ==> n2) -> (APlus a1 a2) ==> (n1 + n2)
| E_AMinus (a1 a2 : aexp) (n1 n2 : nat) :
    (a1 ==> n1) -> (a2 ==> n2) -> (AMinus a1 a2) ==> (n1 - n2)
| E_AMult (a1 a2 : aexp) (n1 n2 : nat) :
    (a1 ==> n1) -> (a2 ==> n2) -> (AMult a1 a2) ==> (n1 * n2)

where "a '==>' n" := (aevalR a n) : type_scope.
End aevalR_extended.

Definition state := total_map nat.

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string) (* <--- NEW *)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).
  
Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).
  
Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Declare Custom Entry com.
Declare Scope com_scope.

Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y" := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y" := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y" := (AMult x y) (in custom com at level 40, left associativity).
Notation "'true'" := true (at level 1).
Notation "'true'" := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y" := (BLe x y) (in custom com at level 70, no associativity).
Notation "x > y" := (BGt x y) (in custom com at level 70, no associativity).
Notation "x = y" := (BEq x y) (in custom com at level 70, no associativity).
Notation "x <> y" := (BNeq x y) (in custom com at level 70, no associativity).
Notation "x && y" := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b" := (BNot b) (in custom com at level 75, right associativity).
Open Scope com_scope.

Definition example_aexp : aexp := <{ 3 + (X * 2) }>.
Definition example_bexp : bexp := <{ true && ~(X <= 4) }>.


Fixpoint aeval (st : state) (* <--- NEW *) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x (* <--- NEW *)
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (* <--- NEW *) (b : bexp) : bool :=
  match b with
  | <{true}> => true
  | <{false}> => false
  | <{a1 = a2}> => (aeval st a1) =? (aeval st a2)
  | <{a1 <> a2}> => negb ((aeval st a1) =? (aeval st a2))
  | <{a1 <= a2}> => (aeval st a1) <=? (aeval st a2)
  | <{a1 > a2}> => negb ((aeval st a1) <=? (aeval st a2))
  | <{~ b1}> => negb (beval st b1)
  | <{b1 && b2}> => andb (beval st b1) (beval st b2)
  end.
  
Definition empty_st := (_ !-> 0).

Notation "x '!->' v" := (x !-> v ; empty_st) (at level 100).
Example aexp1 :
    aeval (X !-> 5) <{ 3 + (X * 2) }>
  = 13.
Proof. reflexivity. Qed.

Example aexp2 :
    aeval (X !-> 5 ; Y !-> 4) <{ Z + (X * Y) }>
  = 20.
Proof. reflexivity. Qed.

Example bexp1 :
    beval (X !-> 5) <{ true && ~(X <= 4) }>
  = true.
Proof. reflexivity. Qed.

Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).
  
Notation "'skip'" := CSkip (in custom com at level 0) : com_scope.
Notation "x := y" := (CAsgn x y) (in custom com at level 0, x constr at level 0, y at level 85, no associativity) : com_scope.
Notation "x ; y" := (CSeq x y) (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" := (CIf x y z) (in custom com at level 89, x at level 99, y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" := (CWhile x y) (in custom com at level 89, x at level 99, y at level 99) : com_scope.

Definition fact_in_coq : com :=
  <{ Z := X;
     Y := 1;
     while Z <> 0 do
       Y := Y * Z;
       Z := Z - 1
     end }>.
Print fact_in_coq.

Unset Printing Notations.
Print fact_in_coq.
(* ===>
   fact_in_coq =
   CSeq (CAsgn Z X)
        (CSeq (CAsgn Y (S O))
              (CWhile (BNot (BEq Z O))
                      (CSeq (CAsgn Y (AMult Y Z))
                            (CAsgn Z (AMinus Z (S O))))))
        : com *)
Set Printing Notations.
Print example_bexp.
(* ===> example_bexp = <{(true && ~ (X <= 4))}> *)
Set Printing Coercions.
Print example_bexp.
(* ===> example_bexp = <{(true && ~ (AId X <= ANum 4))}> *)
Print fact_in_coq.
(* ===>
  fact_in_coq =
  <{ Z := (AId X);
     Y := (ANum 1);
     while ~ (AId Z) = (ANum 0) do
       Y := (AId Y) * (AId Z);
       Z := (AId Z) - (ANum 1)
     end }>
       : com *)
Unset Printing Coercions.

Locate aexp.

Locate "&&".
Locate ";".
Locate "while".

Definition plus2 : com :=
  <{ X := X + 2 }>.
  
Definition XtimesYinZ : com :=
  <{ Z := X * Y }>.
  
Definition subtract_slowly_body : com :=
  <{ Z := Z - 1 ;
     X := X - 1 }>.
     
Definition subtract_slowly : com :=
  <{ while X <> 0 do
       subtract_slowly_body
     end }>.
Definition subtract_3_from_5_slowly : com :=
  <{ X := 3 ;
     Z := 5 ;
     subtract_slowly }>.

Definition loop : com :=
  <{ while true do
       skip
     end }>.

Fixpoint ceval_fun_no_while (st : state) (c : com) : state :=
 match c with
   | <{ skip }> =>
       st
   | <{ x := a }> =>
       (x !-> (aeval st a) ; st)
   | <{ c1 ; c2 }> =>
       let st' := ceval_fun_no_while st c1 in
       ceval_fun_no_while st' c2
   | <{ if b then c1 else c2 end}> =>
       if (beval st b)
         then ceval_fun_no_while st c1
         else ceval_fun_no_while st c2
   | <{ while b do c end }> =>
       st (* bogus *)
 end.
 
Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).

Inductive ceval : com -> state -> state -> Prop :=
| E_Skip : forall st,
    st =[ skip ]=> st
| E_Asgn : forall st a n x,
    aeval st a = n ->
    st =[ x := a ]=> (x !-> n ; st)
| E_Seq : forall c1 c2 st st' st'',
    st =[ c1 ]=> st' ->
    st' =[ c2 ]=> st'' ->
    st =[ c1 ; c2 ]=> st''
| E_IfTrue : forall st st' b c1 c2,
    beval st b = true ->
    st =[ c1 ]=> st' ->
    st =[ if b then c1 else c2 end]=> st'
| E_IfFalse : forall st st' b c1 c2,
    beval st b = false ->
    st =[ c2 ]=> st' ->
    st =[ if b then c1 else c2 end]=> st'
| E_WhileFalse : forall b st c,
    beval st b = false ->
    st =[ while b do c end ]=> st
| E_WhileTrue : forall st st' st'' b c,
    beval st b = true ->
    st =[ c ]=> st' ->
    st' =[ while b do c end ]=> st'' ->
    st =[ while b do c end ]=> st''

where "st =[ c ]=> st'" := (ceval c st st').

Example ceval_example1:
  empty_st =[
     X := 2;
     if (X <= 1)
       then Y := 3
       else Z := 4
     end
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  (* We must supply the intermediate state *)
  apply E_Seq with (X !-> 2).
  - (* assignment command *)
    apply E_Asgn. reflexivity.
  - (* if command *)
    apply E_IfFalse.
    + reflexivity.
    + apply E_Asgn. reflexivity.
Qed.

Example ceval_example2:
  empty_st =[
    X := 0;
    Y := 1;
    Z := 2
  ]=> (Z !-> 2 ; Y !-> 1 ; X !-> 0).
Proof.
  apply E_Seq with (X !-> 0).
  - apply E_Asgn. reflexivity.
  - apply E_Seq with (Y !-> 1; X !-> 0).
    + apply E_Asgn. simpl. reflexivity.
    + apply E_Asgn. simpl. reflexivity.
Qed.

Definition pup_to_n : com
  := <{ Y := 0;
        while X > 0 do
          Y := Y + X;
          X := X - 1
        end }>.

Theorem pup_to_2_ceval :
(X !-> 2) =[
  pup_to_n
]=> (X !-> 0 ; Y !-> 3 ; X !-> 1 ; Y !-> 2 ; Y !-> 0 ; X !-> 2).
Proof.
  Proof.
    apply E_Seq with (Y !-> 0 ; X !-> 2).
    + apply E_Asgn. reflexivity.
    + apply E_WhileTrue with (X !-> 1 ; Y !-> 2 ; Y !-> 0 ; X !-> 2).
      - reflexivity.
      - apply E_Seq with (Y !-> 2 ; Y !-> 0 ; X !-> 2).
        * apply E_Asgn. reflexivity.
        * apply E_Asgn. reflexivity.
      - apply E_WhileTrue with (X !-> 0 ; Y !-> 3 ; X !-> 1 ; Y !-> 2 ; Y !-> 0 ; X !-> 2).
        * reflexivity.
        * apply E_Seq with (Y !-> 3 ; X !-> 1 ; Y !-> 2 ; Y !-> 0 ; X !-> 2).
          -- apply E_Asgn. reflexivity.
          -- apply E_Asgn. reflexivity.
        * apply E_WhileFalse. reflexivity.
  Qed.

  Theorem ceval_deterministic: forall c st st1 st2,
  st =[ c ]=> st1 ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
intros c st st1 st2 E1 E2.
generalize dependent st2.
induction E1; intros st2 E2; inversion E2; subst.
- (* E_Skip *) reflexivity.
- (* E_Asgn *) reflexivity.
- (* E_Seq *)
 rewrite (IHE1_1 st'0 H1) in *.
 apply IHE1_2. assumption.
- (* E_IfTrue, b evaluates to true *)
   apply IHE1. assumption.
- (* E_IfTrue,  b evaluates to false (contradiction) *)
   rewrite H in H5. discriminate.
- (* E_IfFalse, b evaluates to true (contradiction) *)
   rewrite H in H5. discriminate.
- (* E_IfFalse, b evaluates to false *)
   apply IHE1. assumption.
- (* E_WhileFalse, b evaluates to false *)
 reflexivity.
- (* E_WhileFalse, b evaluates to true (contradiction) *)
 rewrite H in H2. discriminate.
- (* E_WhileTrue, b evaluates to false (contradiction) *)
 rewrite H in H4. discriminate.
- (* E_WhileTrue, b evaluates to true *)
 rewrite (IHE1_1 st'0 H3) in *.
 apply IHE1_2. assumption. Qed.
 
Theorem plus2_spec : forall st n st',
  st X = n -> st =[ plus2 ]=> st' -> st' X = n + 2.
Proof.
  intros st n st' HX Heval.
  inversion Heval. subst. clear Heval. simpl.
  apply t_update_eq.
Qed.

Theorem XtimesYinZ_spec : forall st n m st',
  st X = n ->
  st Y = m ->
  st =[ XtimesYinZ ]=> st' ->
  st' Z = n * m.
Proof.
  intros st n m st' Hx Hy Heval.
  inversion Heval. subst. clear Heval.
  apply t_update_eq.
Qed.

Theorem loop_never_stops : forall st st',
  ~(st =[ loop ]=> st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember <{ while true do skip end }> as loopdef
           eqn:Heqloopdef.
  induction contra; try discriminate.
  + inversion Heqloopdef. subst. discriminate.
  + inversion Heqloopdef. subst. apply IHcontra2. reflexivity.
Qed.

Fixpoint no_whiles (c : com) : bool :=
  match c with
  | <{ skip }> =>
      true
  | <{ _ := _ }> =>
      true
  | <{ c1 ; c2 }> =>
      andb (no_whiles c1) (no_whiles c2)
  | <{ if _ then ct else cf end }> =>
      andb (no_whiles ct) (no_whiles cf)
  | <{ while _ do _ end }> =>
      false
  end.
 
Inductive no_whilesR: com -> Prop :=
  | no_whiles_skip : no_whilesR <{ skip}>
  | no_whiles_asgn : forall x a, no_whilesR <{ x := a}>
  | no_whiles_seq : forall c1 c2 (H1 : no_whilesR c1) (H2 : no_whilesR c2), no_whilesR <{c1; c2}>
  | no_whiles_if : forall b ct cf (H1 : no_whilesR ct) (H2 : no_whilesR cf), no_whilesR <{ if b then ct else cf end }>
  .
    
Theorem no_whiles_eqv: 
  forall c, no_whiles c = true <-> no_whilesR c.
Proof.
  intros.
  split.
  - induction c;
    try constructor;
    try (inversion H as [H1]; apply andb_true_iff in H1);
    try (destruct H1 as [H1 _]; apply IHc1; apply H1);
    try (destruct H1 as [_ H1]; apply IHc2; apply H1).
    discriminate.
  - intros H.
    induction H;
    try simpl; try reflexivity; apply andb_true_iff; split; assumption.
Qed.


Theorem no_whiles_terminating : 
  forall c, no_whilesR c -> forall st, exists st', st =[ c ]=> st'.
Proof.
Admitted.

Inductive sinstr : Type :=
| SPush (n : nat)
| SLoad (x : string)
| SPlus
| SMinus
| SMult.

Fixpoint s_execute (st : state) (stack : list nat) (prog : list sinstr) : list nat :=
  match prog, stack with
  | [], _ => stack
  | (SPush n) :: xprog, stack  => s_execute st (n :: stack) xprog
  | (SLoad x) :: xprog, stack  => s_execute st ((st x) :: stack) xprog
  | SPlus :: xprog, n2 :: n1 :: xstack => s_execute st ((n1 + n2) :: xstack) xprog
  | SMinus :: xprog, n2 :: n1 :: xstack => s_execute st ((n1 - n2) :: xstack) xprog
  | SMult :: xprog, n2 :: n1 :: xstack => s_execute st ((n1 * n2) :: xstack) xprog
  | _, _ => stack
  end.

Example s_execute1 :
     s_execute empty_st []
       [SPush 5; SPush 3; SPush 1; SMinus]
   = [2; 5].
Proof.
  simpl. reflexivity.
Qed.

Example s_execute2 :
     s_execute (X !-> 3) [3;4]
       [SPush 4; SLoad X; SMult; SPlus]
   = [15; 4].
Proof.
  simpl. reflexivity.
Qed.


Fixpoint s_compile (e : aexp) : list sinstr :=
  match e with
  | ANum n => [SPush n]
  | AId x => [SLoad x]
  | APlus a1 a2 => (s_compile a1) ++ (s_compile a2) ++ [SPlus]
  | AMinus a1 a2 => (s_compile a1) ++ (s_compile a2) ++ [SMinus]
  | AMult a1 a2 => (s_compile a1) ++ (s_compile a2) ++ [SMult]
  end.

Example s_compile1 :
  s_compile <{ X - (2 * Y) }>
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
Proof.
  simpl. reflexivity.
Qed.

Theorem execute_app : forall st p1 p2 stack,
  s_execute st stack (p1 ++ p2) = s_execute st (s_execute st stack p1) p2.
Proof.
  intros st p1 p2.
  induction p1.
  - simpl. reflexivity.
  - intros stack. destruct a. 
    + destruct stack.
      * simpl. apply IHp1.
      * apply IHp1.
    + simpl. apply IHp1.
Admitted.

Lemma s_compile_correct_aux : forall st e stack,
  s_execute st stack (s_compile e) = aeval st e :: stack.
Proof.
  intros st e.
  induction e.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - intros. simpl. rewrite execute_app. rewrite execute_app.
    rewrite IHe1. rewrite IHe2. simpl. reflexivity.
  - intros. simpl. rewrite execute_app. rewrite execute_app.
    rewrite IHe1. rewrite IHe2. simpl. reflexivity.
  - intros. simpl. rewrite execute_app. rewrite execute_app.
    rewrite IHe1. rewrite IHe2. simpl. reflexivity.
Qed.

Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  intros. rewrite s_compile_correct_aux. reflexivity.
Qed.

Fixpoint beval_short_circuit (st : state) (b : bexp) : bool :=
  match b with
  | <{true}> => true
  | <{false}> => false
  | <{a1 = a2}> => (aeval st a1) =? (aeval st a2)
  | <{a1 <> a2}> => negb ((aeval st a1) =? (aeval st a2))
  | <{a1 <= a2}> => (aeval st a1) <=? (aeval st a2)
  | <{a1 > a2}> => negb ((aeval st a1) <=? (aeval st a2))
  | <{~ b1}> => negb (beval_short_circuit st b1)
  | <{b1 && b2}> => match (beval_short_circuit st b1) with
                    | false => false
                    | true => beval_short_circuit st b2
                    end
  end.

Theorem beval_short_circuit_correct : forall (st : state) (b : bexp),
  beval_short_circuit st b = beval st b.
Proof.
  intros.
  induction b; simpl; reflexivity.
Qed.

Module BreakImp.
