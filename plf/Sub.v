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
  (T->T)->U <: (S->S)->V - false
  ((T->S)->T)->U <: ((S->T)->S)->V - true
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
  | v_pair : forall v1 v2,
    value v1 ->
    value v2 ->
    value <{ (v1, v2)}>
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
      | ST_Pair1 : forall t1 t1' t2,
      t1 --> t1' ->
      <{ (t1, t2) }> --> <{ (t1', t2) }>
  | ST_Pair2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      <{ (v1, t2) }> --> <{ (v1, t2') }>
  | ST_Fst1 : forall t1 t1',
      t1 --> t1' ->
      <{ t1.fst }> --> <{ t1'.fst }>
  | ST_FstPair : forall v1 v2,
      value v1 ->
      value v2 ->
      <{ (v1, v2).fst }> --> <{ v1 }>
  | ST_Snd1 : forall t1 t1',
      t1 --> t1' ->
      <{ t1.snd }> --> <{ t1'.snd }>
  | ST_SndPair : forall v1 v2,
      value v1 ->
      value v2 ->
      <{ (v1, v2).snd }> --> <{ v2 }>

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

Definition context := partial_map ty.
Reserved Notation "Gamma '|--' t '\in' T" (at level 40,
                                          t custom stlc, T custom stlc at level 0).
Inductive has_type : context -> tm -> ty -> Prop :=
  (* Same as before: *)
  (* pure STLC *)
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      Gamma |-- x \in T1
  | T_Abs : forall Gamma x T1 T2 t1,
      (x |-> T2 ; Gamma) |-- t1 \in T1 ->
      Gamma |-- \x:T2, t1 \in (T2 -> T1)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |-- t1 \in (T2 -> T1) ->
      Gamma |-- t2 \in T2 ->
      Gamma |-- t1 t2 \in T1
  | T_True : forall Gamma,
       Gamma |-- true \in Bool
  | T_False : forall Gamma,
       Gamma |-- false \in Bool
  | T_If : forall t1 t2 t3 T1 Gamma,
       Gamma |-- t1 \in Bool ->
       Gamma |-- t2 \in T1 ->
       Gamma |-- t3 \in T1 ->
       Gamma |-- if t1 then t2 else t3 \in T1
  | T_Unit : forall Gamma,
      Gamma |-- unit \in Unit
  (* New rule of subsumption: *)
  | T_Sub : forall Gamma t1 T1 T2,
      Gamma |-- t1 \in T1 ->
      T1 <: T2 ->
      Gamma |-- t1 \in T2
  | T_Pair : forall Gamma t1 T1 t2 T2,
      Gamma |-- t1 \in T1 ->
      Gamma |-- t2 \in T2 ->
      Gamma |-- (t1, t2) \in (T1 * T2)
  | T_Fst : forall Gamma t0 T1 T2,
      Gamma |-- t0 \in (T1*T2) ->
      Gamma |-- t0.fst \in T1
  | T_Snd : forall Gamma t0 T1 T2,
      Gamma |-- t0 \in (T1*T2) ->
      Gamma |-- t0.snd \in T2

where "Gamma '|--' t '\in' T" := (has_type Gamma t T).
Hint Constructors has_type : core.
Module Examples2.
Import Examples.

Example typing_example_neg_one:
  empty |-- (\z:A, z) \in (A->A).
Proof with eauto.
  auto.
Qed.

Example typing_example_neg_two:
  empty |-- (true, true) \in (Bool * Bool).
Proof with eauto.
  auto.
Qed.

Example typing_example_0:
  forall A B,
  empty |-- ((\z:A, z), (\z:B, z)) \in (A->A * B->B).
Proof with eauto.
  intros.
  (* eapply T_Pair. *)
  Admitted.
  
Example typing_example_almost_1:
  forall B,
  empty |-- (\x:(Top * B->B), x.snd) \in (B->B).
Proof with eauto.
  intros. 
  (* eapply T_Snd. *)
  Admitted.
  
(* empty |-- (\x:(Top * B->B). x.snd) ((\z:A.z), (\z:B.z))
         ∈ B->B *)
(* FILL IN HERE *)

(* empty |-- (\z:(C->C)->(Top * B->B). (z (\x:C.x)).snd)
              (\z:C->C. ((\z:A.z), (\z:B.z)))
         ∈ B->B *)
(* FILL IN HERE *)

End Examples2.

Lemma sub_inversion_Bool : forall U,
     U <: <{Bool}> ->
     U = <{Bool}>.
Proof with auto.
  intros U Hs.
  remember <{Bool}> as V.
  induction Hs; try solve_by_invert...
  assert (U = T)... subst...
Qed.

Lemma sub_inversion_arrow : forall U V1 V2,
     U <: <{V1->V2}> ->
     exists U1 U2,
     U = <{U1->U2}> /\ V1 <: U1 /\ U2 <: V2.
Proof with eauto.
  intros U V1 V2 Hs.
  remember <{V1->V2}> as V.
  generalize dependent V2. generalize dependent V1.
  induction Hs; intros; try solve_by_invert...
  - apply IHHs2 in HeqV. destruct HeqV as [T1 [T2 [H1 [H2 H3]]]].
    apply IHHs1 in H1. destruct H1 as [T1' [T2' [H1' [H2' H3']]]].
    exists T1', T2'...
  - inversion HeqV. subst...
Qed.

Lemma sub_inversion_Unit : forall U,
     U <: <{Unit}> ->
     U = <{Unit}>.
Proof with auto.
  intros U Hs.
  remember <{Unit}> as V.
  induction Hs; subst...
  - try solve_by_invert.
    eauto.
 Admitted.
 
 Lemma sub_inversion_Base : forall U s,
  U <: <{Base s}> ->
  U = <{Base s}>.
Proof.
  intros U s Hs.
  remember <{Base s}> as V.
  (* FILL IN HERE *) Admitted.

  Lemma sub_inversion_Top : forall U,
  <{ Top }> <: U ->
  U = <{ Top }>.
Proof with auto.
  intros U Hs.
  remember <{Top}> as V.
  induction Hs; try solve_by_invert...
  - subst.
  Admitted.
  
Lemma canonical_forms_of_arrow_types : forall Gamma s T1 T2,
  Gamma |-- s \in (T1->T2) ->
  value s ->
  exists x S1 s2,
     s = <{\x:S1,s2}>.
Proof with eauto.
  intros.
  induction H; try solve_by_invert.
 Admitted.
  
Lemma canonical_forms_of_Bool : forall Gamma s,
  Gamma |-- s \in Bool ->
  value s ->
  s = tm_true \/ s = tm_false.
Proof with eauto.
  intros Gamma s Hty Hv.
  remember <{Bool}> as T.
  induction Hty; try solve_by_invert...
  - (* T_Sub *)
    subst. apply sub_inversion_Bool in H. subst...
Qed.


Theorem progress : forall t T,
     empty |-- t \in T ->
     value t \/ exists t', t --> t'.
Proof with eauto.
  intros t T Ht.
  remember empty as Gamma.
  induction Ht; subst Gamma; auto.
  - (* T_Var *)
    discriminate.
  - (* T_App *)
    right.
    destruct IHHt1; subst...
    + (* t1 is a value *)
      destruct IHHt2; subst...
      * (* t2 is a value *)
        eapply canonical_forms_of_arrow_types in Ht1; [|assumption].
        destruct Ht1 as [x [S1 [s2 H1]]]. subst.
        exists (<{ [x:=t2]s2 }>)...
      * (* t2 steps *)
        destruct H0 as [t2' Hstp]. exists <{ t1 t2' }>...
    + (* t1 steps *)
      destruct H as [t1' Hstp]. exists <{ t1' t2 }>...
  - (* T_If *)
    right.
    destruct IHHt1.
    + (* t1 is a value *) eauto.
    + apply canonical_forms_of_Bool in Ht1; [|assumption].
      destruct Ht1; subst...
    + destruct H. rename x into t1'. eauto.
  - (* ST_Pair2 *)
    right.
    destruct IHHt1; subst...
    + destruct H; subst...
    Admitted.

Lemma typing_inversion_abs : forall Gamma x S1 t2 T,
  Gamma |-- \x:S1,t2 \in T ->
  exists S2,
    <{S1->S2}> <: T
    /\ (x |-> S1 ; Gamma) |-- t2 \in S2.
Proof with eauto.
 intros Gamma x S1 t2 T H.
 remember <{\x:S1,t2}> as t.
 induction H;
   inversion Heqt; subst; intros; try solve_by_invert.
 - (* T_Abs *)
   exists T1...
 - (* T_Sub *)
   destruct IHhas_type as [S2 [Hsub Hty]]...
 Qed.
 
Lemma typing_inversion_var : forall Gamma (x:string) T,
  Gamma |-- x \in T ->
  exists S,
    Gamma x = Some S /\ S <: T.
Proof with eauto.
  intros Gamma x T H.
  Admitted.

Lemma typing_inversion_app : forall Gamma t1 t2 T2,
  Gamma |-- t1 t2 \in T2 ->
  exists T1,
    Gamma |-- t1 \in (T1->T2) /\
    Gamma |-- t2 \in T1.
Proof with eauto.
  (* FILL IN HERE *) Admitted.
  
Lemma typing_inversion_unit : forall Gamma T,
  Gamma |-- unit \in T ->
    <{Unit}> <: T.
Proof with eauto.
  intros Gamma T Htyp. remember <{ unit }> as tu.
  induction Htyp;
    inversion Heqtu; subst; intros...
Qed.

Lemma abs_arrow : forall x S1 s2 T1 T2,
  empty |-- \x:S1,s2 \in (T1->T2) ->
     T1 <: S1
  /\ (x |-> S1 ; empty) |-- s2 \in T2.
Proof with eauto.
  intros x S1 s2 T1 T2 Hty.
  apply typing_inversion_abs in Hty.
  destruct Hty as [S2 [Hsub Hty1]].
  apply sub_inversion_arrow in Hsub.
  destruct Hsub as [U1 [U2 [Heq [Hsub1 Hsub2]]]].
  injection Heq as Heq; subst... Qed.
  
  
Lemma weakening : forall Gamma Gamma' t T,
  includedin Gamma Gamma' ->
  Gamma |-- t \in T ->
  Gamma' |-- t \in T.
Proof.
intros Gamma Gamma' t T H Ht.
generalize dependent Gamma'.
induction Ht; eauto using includedin_update.
Qed.

Corollary weakening_empty : forall Gamma t T,
  empty |-- t \in T ->
  Gamma |-- t \in T.
Proof.
intros Gamma t T.
eapply weakening.
discriminate.
Qed.

Lemma substitution_preserves_typing : forall Gamma x U t v T,
   (x |-> U ; Gamma) |-- t \in T ->
   empty |-- v \in U ->
   Gamma |-- [x:=v]t \in T.
Proof.
  intros Gamma x U t v T Ht Hv.
  remember (x |-> U; Gamma) as Gamma'.
  generalize dependent Gamma.
  induction Ht; intros Gamma' G; simpl; eauto.
 (* FILL IN HERE *) Admitted.
 
 
Theorem preservation : forall t t' T,
 empty |-- t \in T ->
 t --> t' ->
 empty |-- t' \in T.
Proof with eauto.
intros t t' T HT. generalize dependent t'.
remember empty as Gamma.
induction HT;
   intros t' HE; subst;
   try solve [inversion HE; subst; eauto].
- (* T_App *)
inversion HE; subst...
(* Most of the cases are immediate by induction,
   and eauto takes care of them *)
+ (* ST_AppAbs *)
  destruct (abs_arrow _ _ _ _ _ HT1) as [HA1 HA2].
  apply substitution_preserves_typing with T0...
  Admitted.
  
Module FormalThoughtExercises.
Import Examples.
Notation p := "p".
Notation a := "a".
Definition TF P := P \/ ~P.
  
Theorem formal_subtype_instances_tf_1a:
  TF (forall S T U V, S <: T -> U <: V ->
         <{T->S}> <: <{T->S}>).
Proof.
  unfold TF. left.
  intros.
  apply S_Arrow; apply S_Refl.
Qed.

Theorem formal_subtype_instances_tf_1b:
  TF (forall S T U V, S <: T -> U <: V ->
         <{Top->U}> <: <{S->Top}>).
Proof.
  unfold TF. left. intros.
  apply S_Arrow; apply S_Top.
Qed.

Theorem formal_subtype_instances_tf_1c:
  TF (forall S T U V, S <: T -> U <: V ->
         <{(C->C)->(A*B)}> <: <{(C->C)->(Top*B)}>).
Proof.
  unfold TF. left. intros.
  apply S_Arrow.
  - apply S_Refl.
  - apply S_Prod.
    + apply S_Top.
    + apply S_Refl.
Qed.

Theorem formal_subtype_instances_tf_1d:
  TF (forall S T U V, S <: T -> U <: V ->
         <{T->(T->U)}> <: <{S->(S->V)}>).
Proof.
  unfold TF. right. unfold not. intros contra.
  specialize contra with (T := <{Top}>).
  specialize contra with (V := <{Top}>).
  specialize contra with (U := <{Bool}>).
  specialize contra with (S := <{Unit}>).
  Admitted.

Theorem formal_subtype_instances_tf_1e:
  TF (forall S T U V, S <: T -> U <: V ->
         <{(T->T)->U}> <: <{(S->S)->V}>).
Proof with eauto.
Admitted.

Theorem formal_subtype_instances_tf_1f:
  TF (forall S T U V, S <: T -> U <: V ->
         <{((T->S)->T)->U}> <: <{((S->T)->S)->V}>).
Proof with eauto.
  unfold TF. left. intros.
  apply S_Arrow...
Qed.


Theorem formal_subtype_instances_tf_1g:
  TF (forall S T U V, S <: T -> U <: V ->
         <{S*V}> <: <{T*U}>).
Proof with eauto.
Admitted.

End FormalThoughtExercises.
End STLCSub.
  


  

