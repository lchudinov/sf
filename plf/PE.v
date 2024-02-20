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
