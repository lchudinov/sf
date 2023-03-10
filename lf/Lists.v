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

Definition bag := natlist.

Fixpoint count (v : nat) (s : bag) : nat :=
  match s with
  | [] => 0
  | h :: t => if v =? h then S (count v t) else count v t
  end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. simpl. reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. simpl. reflexivity. Qed.

Definition sum : bag -> bag -> bag :=
  app.
Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.

Definition add (v : nat) (s : bag) : bag :=
  v :: s.
Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Fixpoint member (v : nat) (s : bag) : bool :=
  match s with
  | [] => false
  | h :: t => if h =? v then true else member v t
  end.

Example test_member1: member 1 [1;4;1] = true.
Proof. simpl. reflexivity. Qed.
Example test_member2: member 2 [1;4;1] = false.
Proof. simpl. reflexivity. Qed.

Fixpoint remove_one (v : nat) (s : bag) : bag :=
  match s with
  | [] => []
  | h :: t => if v =? h then t else h :: (remove_one v t)
  end.
Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
  Proof. simpl. reflexivity. Qed.
Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
  Proof. simpl. reflexivity. Qed.
Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
  Proof. simpl. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
  | [] => []
  | h :: t => if h =? v then remove_all v t else h :: (remove_all v t)
  end.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. simpl. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. simpl. reflexivity. Qed.

Fixpoint included (s1 : bag) (s2 : bag) : bool :=
  match s1 with
  | [] => true
  | h :: t => if member h s2 then included t (remove_one h s2) else false
  end.
  
Example test_included1: included [1;2] [2;1;4;1] = true.
Proof. simpl. reflexivity. Qed.
Example test_included2: included [1;2;2] [2;1;4;1] = false.
Proof. simpl. reflexivity. Qed.

Theorem add_inc_count: forall (n: nat) (s : natlist),
  count n (add n s) = S (count n s).
Proof.
  intros n s.
  simpl.
  rewrite eqb_refl.
  reflexivity.
Qed.

Theorem nil_app : forall lst : natlist,
  [] ++ lst = lst.
Proof. simpl. reflexivity. Qed.

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l.
  destruct l as [|h t].
  - simpl. reflexivity.
  - simpl. reflexivity. 
Qed.

Theorem app_assoc : forall lst1 lst2 lst3 : natlist,
  (lst1 ++ lst2) ++ lst3 = lst1 ++ (lst2 ++ lst3).
Proof.
  intros lst1 lst2 lst3.
  induction lst1 as [| h1 t1].
  - (* Set Printing Parentheses. Set Printing All. *) simpl. reflexivity. 
  - simpl. rewrite IHt1. reflexivity.
Qed.

Fixpoint rev (lst:natlist) : natlist :=
  match lst with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.

Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example test_rev2: rev [] = [].
Proof. reflexivity. Qed.

Theorem rev_length_firsttry : forall (lst : natlist),
  length (rev lst) = length lst.
Proof.
  intros lst. induction lst as [| h t].
  -  reflexivity.
  - simpl. rewrite <- IHt. (* Set Printing All. *)
Abort.

Theorem app_length : forall (lst1 lst2 : natlist),
  length (lst1 ++ lst2) = length lst1 + length lst2.
Proof.
  intros lst1 lst2. induction lst1 as [| h1 t1].
  - simpl. reflexivity.
  - simpl. rewrite IHt1. reflexivity.
Qed.

Theorem rev_length : forall (lst : natlist),
  length (rev lst) = length lst.
Proof.
  intros lst. induction lst as [| h t].
  -  reflexivity.
  - simpl. rewrite app_length.
    simpl. rewrite IHt. rewrite add_comm. simpl. reflexivity.
Qed.
Search rev.

Search ( _ + _ = _ + _ ).
Search ( _ + _ = _ + _ ) inside Induction.
Search ( ?x + ?y = ?x + ?y ) inside Induction.

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  intros l. induction l as [| h t].
  - simpl. reflexivity.
  - simpl. rewrite IHt. reflexivity.
Qed.
  
Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2. induction l1 as [| h1 t1].
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite IHt1. rewrite app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros l. induction l as [|h t].
  - simpl. reflexivity.
  - simpl. rewrite rev_app_distr. rewrite IHt. simpl. reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4.
  Set Printing Parentheses.
  rewrite app_assoc.
  rewrite <- app_assoc.
  reflexivity.
Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2.
  induction l1 as [|h1 t1].
  - simpl. reflexivity.
  - simpl. destruct h1.
    -- rewrite IHt1. reflexivity.
    -- rewrite IHt1. reflexivity.
Qed.
  
Fixpoint eqblist (l1 l2 : natlist) : bool :=
  match l1, l2 with
  | [], [] => true
  | [], _ => false
  | _, [] => false
  | h1 :: t1, h2 :: t2 => if h1 =? h2 then eqblist t1 t2 else false
  end.

Example test_eqblist1 :
  (eqblist nil nil = true).
Proof. reflexivity. Qed.
Example test_eqblist2 :
  eqblist [1;2;3] [1;2;3] = true.
Proof. simpl. reflexivity. Qed.
Example test_eqblist3 :
  eqblist [1;2;3] [1;2;4] = false.
Proof. simpl.  reflexivity. Qed.

Theorem eqblist_refl : forall l:natlist,
  true = eqblist l l.
Proof.
  intros l.
  induction l as [|h1 t1].
  - simpl. reflexivity.
  - simpl. rewrite <- IHt1. rewrite eqb_refl. reflexivity.
Qed.

Theorem count_member_nonzero : forall (s : bag),
  1 <=? (count 1 (1 :: s)) = true.
Proof. simpl. reflexivity. Qed.

Theorem leb_n_Sn : forall n : nat,
  n <=? (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl. reflexivity.
  - (* S n' *)
    simpl. rewrite IHn'. reflexivity.
Qed. 

Theorem remove_does_not_increase_count: forall (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
  intros s. induction s as [|h t].
  - simpl. reflexivity.
  - destruct h.
    -- simpl. rewrite leb_n_Sn. reflexivity.
    -- simpl. rewrite IHt. reflexivity.
Qed.

Theorem bag_count_sum : forall (n : nat) (a b : bag),
  count n (sum a b) = count n a + count n b.
Proof.
  intros n a b.
  induction a as [|n' ta].
  - simpl. reflexivity.
  - simpl. destruct (n =? n').
    -- simpl. rewrite <- IHta. reflexivity.
    -- rewrite <- IHta. reflexivity.
Qed.

Theorem involution_injective : forall (f : nat -> nat),
    (forall n : nat, n = f (f n)) -> (forall n1 n2 : nat, f n1 = f n2 -> n1 = n2).
Proof.
  intros.
  rewrite -> H.
  rewrite <- H0.
  rewrite <- H.
  reflexivity.
Qed.

Theorem rev_injective : forall (l1 l2 : natlist),
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2. intros H.
  rewrite <- rev_involutive.
  rewrite <- H.
  rewrite -> rev_involutive.
  reflexivity.
Qed.
  

(** Options *)

Fixpoint nth_bad (lst : natlist) (n : nat) : nat :=
  match lst with
  | [] => 42
  | h :: t => match n with
             | 0 => h
             | S k => nth_bad t k
             end
  end.
    
Inductive natoption : Type :=
  | Some (n : nat)
  | None.

Fixpoint nth_error (lst : natlist) (n : nat) : natoption :=
match lst with
| [] => None
| h :: t => match n with
           | 0 => Some h
           | S k => nth_error t k
           end
end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

Fixpoint nth_error' (lst : natlist) (n : nat) : natoption :=
match lst, n with
| [], _ => None
| h :: _, 0 => Some h
| _ :: t, S k => nth_error' t k
end.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

Definition hd_error (l : natlist) : natoption :=
  match l with
  | [] => None
  | hd :: _ => Some hd
  end.
Example test_hd_error1 : hd_error [] = None.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error [1] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof. reflexivity. Qed.

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
  intros l default.
  induction l.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.
End NatList.

Module PartialMap.
Export NatList.

Inductive partial_map : Type :=
| Empty
| Binding (k : nat) (v : nat) (m : partial_map).

(** The [update]  function records a binding for a key. If the key
    was already present, that shadows the old binding. *)
Definition update (k : nat) (v : nat) (m : partial_map) := 
  Binding k v m.

Fixpoint find (k : nat) (m : partial_map) : natoption :=
  match m with
  | Empty => None
  | Binding k_2 v m' =>
    if k =? k_2 then Some v else find k m'
  end.

Theorem find_update: forall (m : partial_map) (k v : nat),
  find k (update k v m) = Some v.
Proof.
  intros m k v. simpl. rewrite eqb_refl. reflexivity.
Qed.
End PartialMap.

Module PartialMap'.
Export NatList.

Inductive id : Type :=
  | Id (n : nat).

Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.

Inductive partial_map : Type :=
| empty
| record (i : id) (v : nat) (m : partial_map).

Theorem eqb_id_refl : forall x, eqb_id x x = true.
Proof. 
  intros x.
  induction x.
  simpl. rewrite eqb_refl. reflexivity.
Qed.

Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty => None
  | record y v d' => if eqb_id x y
                     then Some v
                     else find x d'
  end.
  
Theorem update_eq : forall (d : partial_map) (x : id) (v: nat),
  find x (update d x v) = Some v.
Proof.
  intros d x v.
  simpl. rewrite eqb_id_refl. reflexivity.
Qed.

Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
    eqb_id x y = false -> find x (update d y o) = find x d.
Proof.
  intros x y d o.
  simpl. intros H. rewrite H. reflexivity.
Qed.

Inductive baz : Type :=
  | Baz1 (x : baz)
  | Baz2 (y : baz) (b : bool).

(* How many elements does the type baz have? (Explain in words, in a comment.) *)
(* zero *)
End PartialMap'.