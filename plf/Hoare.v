Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From PLF Require Export Imp.
Set Default Goal Selector "!".

Definition Assertion := state -> Prop.

Module ExAssertions.
Definition assn1 : Assertion := fun st => st X <= st Y.
(* holds for states st in which value of X less or equal of value of Y *)
Definition assn2 : Assertion := fun st => st X = 3 \/ st X <= st Y.
(* holds for states st in which value of X is 3 value of X less or equal of value of Y *)
Definition assn3 : Assertion := fun st => st Z * st Z <= st X /\ ~ (((S (st Z)) * (S (st Z))) <= st X).
(* holds for states st in which value of Z * Z is less of equal than value of X and not sqaure of the number after Z is less or equal than value of X *)
Definition assn4 : Assertion := fun st => st Z = max (st X) (st Y).
(* holds for states st in which value of Z equals max of values X and Y *)
End ExAssertions.


