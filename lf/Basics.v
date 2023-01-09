Require Coq.extraction.Extraction.
Extraction Language Haskell.
From Coq Require Export String.


Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday (d: day) : day := 
  match d with
  | monday => thursday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => saturday
  | saturday => sunday
  | sunday => monday
  end.

Compute (next_weekday friday).
Compute (next_weekday (next_weekday saturday)).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = monday.
Proof. simpl. reflexivity. Qed.

Extraction next_weekday.

Inductive bool : Type :=
  | true
  | false.

Definition negb (b : bool) : bool := 
match b with
| true => false
| false => true 
end.

Definition andb (a: bool) (b: bool) : bool := 
match a with
| true => b
| false => false
end .

Definition orb (a: bool) (b: bool) : bool := 
match a with
| true => true
| false => b
end .

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Compute negb(true).

Notation "a && b":= (andb a b).
Notation "a || b":= (orb a b).

Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

Definition negb' (b : bool) : bool := 
if b then false
else true.

Definition andb' (a: bool) (b: bool) : bool := 
if a then b
else false.

Definition orb' (a: bool) (b: bool) : bool := 
if a then true
else b.

Definition nandb (b1:bool) (b2:bool) : bool :=
  (negb (andb b1 b2)).
Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  (andb b1 (andb b2 b3)).
Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Check true.
Check (negb true).
Check negb.
Check andb.
