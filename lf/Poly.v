From LF Require Export Lists.

Inductive natlist : Type :=
| nat_nil
| nat_cons (n : nat) (lst : natlist).

Inductive boollist : Type :=
| bool_nil
| bool_cons (b : bool) (lst : boollist).

Inductive list (X : Type) :=
| nil
| cons (x : X) (lst : list X).

Check list : Type -> Type.

Check (nil nat) : list nat.

Check (cons nat 3 (nil nat)) : list nat.

Check nil : forall (X : Type), list X.

Check cons : forall (X : Type), X -> list X -> list X.

Check (cons nat 2 (cons nat 2 (nil nat))) : list nat.

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

Example test_repeat_1 : 
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity. Qed.

Example test_repeat_2 : 
  repeat bool false 2 = cons bool false (cons bool false (nil bool)).
Proof. reflexivity. Qed.

Module MumbleGrumble.
Inductive mumble : Type :=
  | a
  | b (x : mumble) (y : nat)
  | c.
Inductive grumble (X:Type) : Type :=
  | d (m : mumble)
  | e (x : X).

(* 
d (b a 5) - No
d mumble (b a 5) - Yes
d bool (b a 5) - No
e bool true - Yes
e mumble (b c 0) - Yes
e bool (b c 0) - No
c - No
*)
End MumbleGrumble.

Fixpoint repeat' X x count : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat' X x count')
  end.

Check repeat' : forall X : Type, X -> nat -> list X.

Fixpoint repeat'' X x count : list X :=
  match count with
  | 0 => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.
  
Definition  list_123 := cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.

Definition  list_123'' := cons 1 (cons 2 (cons 3 nil)).

Fixpoint repeat''' {X: Type} (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil
  | S count' => cons x (repeat''' x count')
  end.

Fixpoint app {X : Type} (l_1 l_2 : list X) : list X :=
  match l_1 with
  | nil => l_2
  | cons h t => cons h (app t l_2)
  end.

Fixpoint rev {X : Type} (l : list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ t => S (length t)
  end.

  Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity. Qed.

Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. reflexivity. Qed.

Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity. Qed.

Fail Definition mynil := nil.

Definition mynil : list nat := nil.

Check @nil : forall X : Type, list X.

Definition mynil' := @nil nat.

Definition mynil'' := @nil. Check mynil''.

Notation "x :: y" :=
  (cons x y)
  (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) .. ).
Notation "x ++ y" :=
  (app x y)
  (at level 60, right associativity).

Definition list_123''' := [1; 2; 3].

Theorem app_assoc : forall X (lst1 lst2 lst3 : list X),
  (lst1 ++ lst2) ++ lst3 = lst1 ++ (lst2 ++ lst3).
Proof.
  intros X lst1 lst2 lst3.
  induction lst1 as [| h1 t1].
  - simpl. reflexivity. 
  - simpl. rewrite IHt1. reflexivity.
Qed.

Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof.
  intros X l.
  induction l as [|h t].
  - simpl. reflexivity.
  - simpl. rewrite IHt. reflexivity.
Qed.

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros X l1 l2.
  induction l1 as [|h1 t1].
  - simpl. reflexivity.
  - simpl. rewrite IHt1. reflexivity.
Qed.