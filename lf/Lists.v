From LF Require Export Induction.
Module NatList.

Inductive natprod : Type :=
  | pair (n_1 n_2 : nat).

Check (pair 3 5).

Definition fst (p : natprod) : nat :=
  match p with
  | pair x _ => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair _ y => y
  end.
  
Compute (fst (pair 3 5)).

Notation "( x , y )" := (pair x y).

Compute (fst (3, 5)).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x, _) => x
  end.

Definition snd' (p : natprod) : nat :=
  match p with
  | (_, y) => y
  end.
  
Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x, y) => (y, x)
  end.

Theorem  surjective_pairing': forall n m : nat,
  (n,m) = (fst (n,m), snd(n,m)). 
Proof.
  simpl. reflexivity.
Qed.

Theorem  surjective_pairing_stuck: forall p : natprod,
  p = (fst p, snd p).
Proof.
  simpl.
Abort.

Theorem  surjective_pairing: forall p : natprod,
  p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity.
Qed.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" :=
  (cons x l)
  (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition mylist_1 := 1 :: (2 :: (3 :: nil)).
Definition mylist_2 := 1 :: 2 :: 3 :: nil.
Definition mylist_3 := [1; 2; 3].

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Compute repeat 42 3.

Fixpoint length (lst : natlist) : nat :=
  match lst with
  | [] => 0
  | _ :: t => S (length t)
  end.

Compute (length (repeat 42 3)).

Fixpoint app(l_1 l_2 : natlist) : natlist :=
  match l_1 with
  | [] => l_2
  | h :: t => h :: (app t l_2)
  end.

Compute (app [1;2;3] [4;5;6]).

Notation "x ++ y" := (app x y)
                    (at level 60 , right associativity).

Example test_app_1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.

Example test_app_2: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.

Example test_app_3: [] ++ [4;5] = [4;5].
Proof. reflexivity. Qed.

Example test_app_4: [1;2;3] ++ [] = [1;2;3].
Proof. reflexivity. Qed.

Definition hd (default : nat) (l : natlist) :=
  match l with
  | [] => default
  | h :: _ => h
  end.

Definition tl (l : natlist) : natlist :=
  match l with
  | [] => []
  | _ :: t => t
  end.

Example test_hd_1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd_2: hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with 
  | [] => []
  | 0 :: t => nonzeros t
  | h :: t => h :: (nonzeros t)
  end.

Example test_nonzeros: nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof.  simpl. reflexivity. Qed.

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | [] => []
  | h :: t => if even h then oddmembers t else h :: (oddmembers t)
  end.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity. Qed.

Definition countoddmembers (l:natlist) : nat := 
  length (oddmembers l).

Example test_countoddmembers1:
countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers2:
countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers3:
countoddmembers nil = 0.
Proof. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
  | [], [] => []
  | h1 :: t, [] => l1
  | [],  h2 :: t2 => l2
  | h1 :: t1, h2 :: t2 => h1 :: h2 :: (alternate t1 t2)
  end.

Example test_alternate1: alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. simpl. reflexivity. Qed.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof. simpl. reflexivity. Qed.
Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof. simpl. reflexivity. Qed.
Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof. simpl. reflexivity. Qed.
