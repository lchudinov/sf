Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
Set Warnings "-deprecated-syntactic-definition".
From Coq Require Import Strings.String.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Lia.
From PLF Require Import Maps.
From PLF Require Import Smallstep.
From Coq Require Import Lists.List. Import Datatypes.
Check length.
Import Nat.

Module STLCRef.

Inductive ty : Type :=
  | Ty_Nat : ty
  | Ty_Unit : ty
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Ref : ty -> ty.
  
Inductive tm : Type :=
  (* STLC with numbers: *)
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  | tm_const : nat -> tm
  | tm_succ : tm -> tm
  | tm_pred : tm -> tm
  | tm_mult : tm -> tm -> tm
  | tm_if0 : tm -> tm -> tm -> tm
  (* new terms *)
  | tm_unit : tm
  | tm_ref : tm -> tm
  | tm_deref : tm -> tm
  | tm_assign : tm -> tm -> tm
  | tm_loc : nat -> tm.
  
Declare Custom Entry stlc.
Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc at level 90, x at level 99,
                     t custom stlc at level 99,
                     y custom stlc at level 99,
                     left associativity).
Coercion tm_var : string >-> tm.
Notation "{ x }" := x (in custom stlc at level 0, x constr).
Notation "'Unit'" :=
  (Ty_Unit) (in custom stlc at level 0).
Notation "'unit'" := tm_unit (in custom stlc at level 0).
Notation "'Nat'" := Ty_Nat (in custom stlc at level 0).
Notation "'succ' x" := (tm_succ x) (in custom stlc at level 0,
                                     x custom stlc at level 0).
Notation "'pred' x" := (tm_pred x) (in custom stlc at level 0,
                                     x custom stlc at level 0).
Notation "x * y" := (tm_mult x y) (in custom stlc at level 1,
                                      left associativity).
Notation "'if0' x 'then' y 'else' z" :=
  (tm_if0 x y z) (in custom stlc at level 89,
                    x custom stlc at level 99,
                    y custom stlc at level 99,
                    z custom stlc at level 99,
                    left associativity).
Coercion tm_const : nat >-> tm.
Notation "'Ref' t" :=
  (Ty_Ref t) (in custom stlc at level 4).
Notation "'loc' x" := (tm_loc x) (in custom stlc at level 2).
Notation "'ref' x" := (tm_ref x) (in custom stlc at level 2).
Notation "'!' x " := (tm_deref x) (in custom stlc at level 2).
Notation " e1 ':=' e2 " := (tm_assign e1 e2) (in custom stlc at level 21).

Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  | v_nat : forall n : nat ,
      value <{ n }>
  | v_unit :
      value <{ unit }>
  | v_loc : forall l,
    value <{ loc l }>.

Hint Constructors value : core.

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  (* pure STLC *)
  | tm_var y =>
      if String.eqb x y then s else t
  | <{\y:T, t1}> =>
      if String.eqb x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
  (* numbers *)
  | tm_const _ =>
      t
  | <{succ t1}> =>
      <{succ [x := s] t1}>
  | <{pred t1}> =>
      <{pred [x := s] t1}>
  | <{t1 * t2}> =>
      <{ ([x := s] t1) * ([x := s] t2)}>
  | <{if0 t1 then t2 else t3}> =>
      <{if0 [x := s] t1 then [x := s] t2 else [x := s] t3}>
  (* unit *)
  | <{ unit }> =>
    <{ unit }>
  (* references *)
  | <{ ref t1 }> =>
      <{ ref ([x:=s] t1) }>
  | <{ !t1 }> =>
      <{ !([x:=s] t1) }>
  | <{ t1 := t2 }> =>
    <{ ([x:=s] t1) := ([x:=s] t2) }>
  | <{ loc _ }> =>
      t
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.
Definition tseq t1 t2 :=
  <{ (\ x : Unit, t2) t1 }>.
Notation "t1 ; t2" := (tseq t1 t2) (in custom stlc at level 3).