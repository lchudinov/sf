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
*)