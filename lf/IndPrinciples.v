Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export ProofObjects.

Check nat_ind :
  forall P : nat -> Prop,
    P 0 ->
    (forall n : nat, P n -> P (S n)) ->
    forall n : nat, P n.

Theorem mul_0_r' : forall n : nat, n * 0 = 0.
Proof.
  apply nat_ind.
  - (* n = 0 *) reflexivity.
  - (* n = Sn' *) simpl. intros n' IHn'. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_one_r' : forall n : nat,
  n + 1 = S n.
Proof.
  apply nat_ind.
  - simpl. reflexivity.
  - intros n' IHn'. simpl. rewrite IHn'. reflexivity.
Qed.

Inductive time : Type :=
  | day
  | night.

Check time_ind :
  forall P : time -> Prop,
  P day ->
  P night ->
  forall t : time, P t.
  
Inductive rgb : Type :=
  | red
  | green
  | blue.
Check rgb_ind :
  forall P : rgb -> Prop,
  P red ->
  P green ->
  P blue ->
  forall c : rgb, P c.
  
Inductive natlist : Type :=
  | nnil
  | ncons (n : nat) (l : natlist).

Check natlist_ind : 
  forall P : natlist -> Prop,
  P nnil ->
  (forall (n : nat) (l : natlist),
    P l -> P (ncons n l)) ->
  forall l : natlist, P l.

Inductive natlist' : Type :=
  | nnil'
  | nsnoc (l : natlist') (n : nat).
  
Check natlist'_ind :
  forall P : natlist' -> Prop,
    P nnil' ->
    (forall l : natlist', P l -> forall n : nat, P (nsnoc l n)) ->
    forall n : natlist', P n.

Inductive booltree : Type :=
  | bt_empty
  | bt_leaf (b : bool)
  | bt_branch (b : bool) (t1 t2 : booltree).
  
Definition booltree_property_type : Type := booltree -> Prop.

Definition base_case (P : booltree_property_type) : Prop :=
  P bt_empty.

Definition leaf_case (P : booltree_property_type) : Prop :=
  forall b : bool, P (bt_leaf b).

Definition branch_case (P : booltree_property_type) : Prop :=
  forall (b : bool) (t1 : booltree), P t1 -> forall t2 : booltree, P t2 -> P (bt_branch b t1 t2).

Definition booltree_ind_type :=
  forall (P : booltree_property_type),
    base_case P ->
    leaf_case P ->
    branch_case P ->
    forall (b : booltree), P b.

Check booltree_ind.

Theorem booltree_ind_type_correct : booltree_ind_type.
Proof.
  exact booltree_ind.
Qed.

Inductive Toy : Type :=
  | con1 (b : bool)
  | con2 (n : nat) (t : Toy)
.

Check Toy_ind.
Theorem Toy_correct : exists f g,
  forall P : Toy -> Prop,
  (forall b : bool, P (f b)) ->
  (forall (n : nat) (t : Toy), P t -> P (g n t)) ->
  forall t : Toy, P t.
Proof.
  exists con1. exists con2. exact Toy_ind.
Qed.
Check list.
Check list_ind.

Inductive tree (X:Type) : Type :=
  | leaf (x : X)
  | node (t1 t2 : tree X).

Check tree_ind.
  
Definition tree_ind_type :=
  forall (X : Type) (P : tree X -> Prop),
  (forall (x : X), P (leaf X x)) ->
  (forall (t1 : tree X), P t1 -> forall (t2 : tree X), P t2 -> P (node X t1 t2)) ->
  (forall (t1 t2 : tree X), P t1 -> P t2 -> P (node X t1 t2)) ->
  forall (t : tree  X), P t.
  
Inductive mytype (X : Type) : Type :=
  | constr1 (x : X)
  | constr2 (n : nat)
  | constr3 (m : mytype X) (n : nat).

Check mytype_ind.

Inductive foo (X Y : Type) :=
  | bar (x : X)
  | baz (y : Y)
  | quux (f1 : nat -> foo X Y).

Check foo_ind.
  
Inductive foo' (X:Type) : Type :=
  | C1 (l : list X) (f : foo' X)
  | C2.

Definition foo''_ind := 
forall (X : Type) (P : foo' X -> Prop),
(forall (l : list X) (f : foo' X),
P f ->
P (C1 X l f)) ->
P (C2 X) ->
forall f : foo' X, P f.

Definition P_m0r (n:nat) : Prop :=
  n * 0 = 0.
Definition P_m0r' : nat -> Prop :=
  fun n => n * 0 = 0.

Theorem mul_0_r'' : forall n:nat,
  P_m0r n.
Proof.
apply nat_ind.
- (* n = O *) reflexivity.
- (* n = S n' *)
  (* Note the proof state at this point! *)
  intros n IHn.
  unfold P_m0r in IHn. unfold P_m0r. simpl. apply IHn.
Qed.

Theorem add_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  (* ...we first introduce all 3 variables into the context,
     which amounts to saying "Consider an arbitrary n, m, and
     p..." *)
  intros n m p.
  (* ...We now use the induction tactic to prove P n (that
     is, n + (m + p) = (n + m) + p) for _all_ n,
     and hence also for the particular n that is in the context
     at the moment. *)
  induction n as [| n'].
  - (* n = O *) reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem add_comm'' : forall n m : nat,
  n + m = m + n.
Proof.
  induction n as [| n'].
  - (* n = O *) intros m. rewrite -> add_0_r. reflexivity.
  - (* n = S n' *) intros m. simpl. rewrite -> IHn'.
    rewrite <- plus_n_Sm. reflexivity.
Qed.

Definition P_add_comm (n m:nat) : Prop :=
  n + m = m + n.

Definition P_add_comm' : nat -> nat -> Prop :=
  fun n =>  fun m => n + m = m + n.

Theorem P_add_comm'' : forall (n m:nat),
P_add_comm n m.
Proof.
  induction n as [|n'].
- (* n = O *) intros m. unfold P_add_comm. simpl. rewrite add_0_r. reflexivity. 
- (* n = S n' *)
  intros m. unfold P_add_comm in IHn'. unfold P_add_comm. simpl. rewrite <- plus_n_Sm. rewrite IHn'. reflexivity.
Qed.

Print ev.

Inductive ev' : nat -> Prop :=
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).
  
Theorem ev_ev' : forall n, ev n -> ev' n.
Proof.
  apply ev_ind.
  - (* ev_0 *)
    apply ev'_0.
  - (* ev_SS *)
    intros m Hm IH.
    apply (ev'_sum 2 m).
    + apply ev'_2.
    + apply IH.
  Qed.

Inductive le1 : nat -> nat -> Prop :=
| le1_n : forall n, le1 n n
| le1_S : forall n m, (le1 n m) -> (le1 n (S m)).
Notation "m <=1 n" := (le1 m n) (at level 70).

Inductive le2 (n : nat) : nat -> Prop :=
  | le2_n : le2 n n
  | le2_S m (H : le2 n m) : le2 n (S m).
Notation "m <=2 n" := (le2 m n) (at level 70).

Check le1_ind :
  forall P : nat -> nat -> Prop,
    (forall n : nat, P n n) ->
    (forall n m : nat, n <=1 m -> P n m -> P n (S m)) ->
    forall n n0 : nat, n <=1 n0 -> P n n0.

Check le2_ind :
  forall (n : nat) (P : nat -> Prop),
    P n ->
    (forall m : nat, n <=2 m -> P m -> P (S m)) ->
    forall n0 : nat, n <=2 n0 -> P n0.