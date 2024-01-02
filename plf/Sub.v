Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From PLF Require Import Types.
From PLF Require Import Smallstep.
Set Default Goal Selector "!".

(*
  T->S <: T->S - true
  Top->U <: S->Top - true
  (C->C) -> (A*B) <: (C->C) -> (Top*B) - true
  T->T->U <: S->S->V - false
  (T->T)->U <: (S->S)->V - true
  ((T->S)->T)->U <: ((S->T)->S)->V - false
  S*V <: T*U - false
*)

(*
  Top
  Top -> Student
  Student -> Person
  Student -> Top
  Person -> Student
  
  Top -> Student
  Person -> Student
  Student -> Person
  Student -> Top
  Top
*)

(*
  forall S T,
  S <: T  ->
  S->S   <:  T->T
  
  false
  
  forall S,
   S <: A->A ->
   exists T,
      S = T->T  /\  T <: A
  
  false
  
  forall S T1 T2,
   (S <: T1 -> T2) ->
   exists S1 S2,
      S = S1 -> S2  /\  T1 <: S1  /\  S2 <: T2 
      
  true
  
  exists S,
   S <: S->S 
   
   false
  
  exists S,
   S->S <: S  
   
   false
  
  forall S T1 T2,
   S <: T1*T2 ->
   exists S1 S2,
      S = S1*S2  /\  S1 <: T1  /\  S2 <: T2  
  true
*)

(*
  Which of the following statements are true, and which are false?
  There exists a type that is a supertype of every other type. - true
  There exists a type that is a subtype of every other type. - false
  There exists a pair type that is a supertype of every other pair type. - true
  There exists a pair type that is a subtype of every other pair type. - false
  There exists an arrow type that is a supertype of every other arrow type. - false
  There exists an arrow type that is a subtype of every other arrow type. - false
  There is an infinite descending chain of distinct types in the subtype relation---that is, an infinite sequence of types S0, S1, etc., such that all the Si's are different and each S(i+1) is a subtype of Si. - true
  There is an infinite ascending chain of distinct types in the subtype relation---that is, an infinite sequence of types S0, S1, etc., such that all the Si's are different and each S(i+1) is a supertype of Si. - false
*)

(*
forall T,
         ~(T = Bool \/ exists n, T = Base n) ->
         exists S,
            S <: T  \/  S <> T
  false, Unit
*)

(*
empty |-- (\p:T*Top. p.fst) ((\z:A.z), unit) \in A->A

A -> A, Top
*)

(*

empty |-- (\p:(A->A * B->B). p) ((\z:A.z), (\z:B.z)) \in T

(A->A * B->B), Top
*)

(*
  a:A |-- (\p:(A*T). (p.snd) (p.fst)) (a, \z:A.z) \in A
  A->A, Top
*)

(*
exists S,
         empty |-- (\p:(A*T). (p.snd) (p.fst)) \in S
A->A->(A->A), Top
*)

(*
exists S t,
        empty |-- (\x:T. x x) t \in S
*)

Module STLCSub.
Inductive ty : Type :=
  | Ty_Top : ty
  | Ty_Bool : ty
  | Ty_Base : string -> ty
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Unit : ty
  | Ty_Prod : ty -> ty -> ty
.

Inductive tm : Type :=
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm
  | tm_unit : tm
  | tm_pair : tm -> tm -> tm
  | tm_fst : tm -> tm
  | tm_snd : tm -> tm
.

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
Notation "'Bool'" := Ty_Bool (in custom stlc at level 0).
Notation "'if' x 'then' y 'else' z" :=
  (tm_if x y z) (in custom stlc at level 89,
                    x custom stlc at level 99,
                    y custom stlc at level 99,
                    z custom stlc at level 99,
                    left associativity).
Notation "'true'" := true (at level 1).
Notation "'true'" := tm_true (in custom stlc at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := tm_false (in custom stlc at level 0).
Notation "'Unit'" :=
  (Ty_Unit) (in custom stlc at level 0).
Notation "'unit'" := tm_unit (in custom stlc at level 0).
Notation "'Base' x" := (Ty_Base x) (in custom stlc at level 0).
Notation "'Top'" := (Ty_Top) (in custom stlc at level 0).
Notation "X * Y" :=
  (Ty_Prod X Y) (in custom stlc at level 2, X custom stlc, Y custom stlc at level 0).
Notation "( x ',' y )" := (tm_pair x y) (in custom stlc at level 0,
                                                x custom stlc at level 99,
                                                y custom stlc at level 99).
Notation "t '.fst'" := (tm_fst t) (in custom stlc at level 1).
Notation "t '.snd'" := (tm_snd t) (in custom stlc at level 1).
Notation "{ x }" := x (in custom stlc at level 1, x constr).

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).
Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if String.eqb x y then s else t
  | <{\y:T, t1}> =>
      if String.eqb x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
  | <{true}> =>
      <{true}>
  | <{false}> =>
      <{false}>
  | <{if t1 then t2 else t3}> =>
      <{if ([x:=s] t1) then ([x:=s] t2) else ([x:=s] t3)}>
  | <{unit}> =>
      <{unit}>
  | <{ (t1, t2) }> =>
      <{( [x:=s] t1, [x:=s] t2 )}>
  | <{t0.fst}> =>
      <{ ([x:=s] t0).fst}>
  | <{t0.snd}> =>
      <{ ([x:=s] t0).snd}>
  end
where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  | v_true :
      value <{true}>
  | v_false :
      value <{false}>
  | v_unit :
      value <{unit}>
.

Hint Constructors value : core.
Reserved Notation "t '-->' t'" (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T2 t1 v2,
         value v2 ->
         <{(\x:T2, t1) v2}> --> <{ [x:=v2]t1 }>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1 t2'}>
  | ST_IfTrue : forall t1 t2,
      <{if true then t1 else t2}> --> t1
  | ST_IfFalse : forall t1 t2,
      <{if false then t1 else t2}> --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      <{if t1 then t2 else t3}> --> <{if t1' then t2 else t3}>
where "t '-->' t'" := (step t t').
Hint Constructors step : core.

Reserved Notation "T '<:' U" (at level 40).
Inductive subtype : ty -> ty -> Prop :=
  | S_Refl : forall T,
      T <: T
  | S_Trans : forall S U T,
      S <: U ->
      U <: T ->
      S <: T
  | S_Top : forall S,
      S <: <{Top}>
  | S_Arrow : forall S1 S2 T1 T2,
      T1 <: S1 ->
      S2 <: T2 ->
      <{S1->S2}> <: <{T1->T2}>
  | S_Prod : forall S1 S2 T1 T2,
      S1 <: T1 ->
      S2 <: T2 ->
      <{S1 * S2}> <: <{T1 * T2}>
where "T '<:' U" := (subtype T U).

Hint Constructors subtype : core.
Module Examples.
Open Scope string_scope.
Notation x := "x".
Notation y := "y".
Notation z := "z".
Notation A := <{Base "A"}>.
Notation B := <{Base "B"}>.
Notation C := <{Base "C"}>.
Notation String := <{Base "String"}>.
Notation Float := <{Base "Float"}>.
Notation Integer := <{Base "Integer"}>.
Example subtyping_example_0 :
  <{C->Bool}> <: <{C->Top}>.
Proof. auto. Qed.

Definition Person : ty :=
  <{ (String * Top) }>.
  Definition Student : ty :=
  <{ (String * Float) }>.
  Definition Employee : ty :=
  <{ (String * Integer) }>.
(* Now use the definition of the subtype relation to prove the following: *)
Example sub_student_person :
  Student <: Person.
Proof. unfold Student. unfold Person. auto. Qed.
Example sub_employee_person :
  Employee <: Person.
Proof. unfold Employee. unfold Person. auto. Qed.

Example subtyping_example_1 :
  <{Top->Student}> <: <{(C->C)->Person}>.
Proof with eauto.
  unfold Student, Person.
  auto.
Qed.

Example subtyping_example_2 :
  <{Top->Person}> <: <{Person->Top}>.
  Proof with eauto.
  unfold Student, Person.
  auto.
Qed.
End Examples.

