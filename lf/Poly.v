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
