Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From PLF Require Import Smallstep.
Set Default Goal Selector "!".
Hint Resolve update_eq : core.

Module STLC.

Inductive ty : Type :=
  | Ty_Bool : ty
  | Ty_Arrow : ty -> ty -> ty.
  
Inductive tm : Type :=
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm.
  
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

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.

Notation idB := <{\x:Bool, x}>.
Notation idBB := <{\x:Bool->Bool, x}>.
Notation idBBBB := <{\x:((Bool->Bool)->(Bool->Bool)), x}>.
Notation k := <{\x:Bool, \y:Bool, x}>.
Notation notB := <{\x:Bool, if x then false else true}>.

Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1, value <{ \x:T2, t1 }>
  | v_true : value <{ true }>
  | v_false : value <{ false }>.
  
Hint Constructors value : core.

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y => if String.eqb x y then s else t
  | <{\y:T, t1}> => if String.eqb x y then <{\y:T, t1}> else <{\y:T, [x:=s] t1}> 
  | <{ t1 t2 }> => <{ ([x:=s] t1) ([x:=s] t2) }>
  | <{ true }> => <{ true }>
  | <{ false }> => <{ false }>
  | <{ if t1 then t2 else t3 }> => <{ if ([x:=s] t1) then ([x:=s] t2) else ([x:=s] t3) }>
  end
where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

Check <{[x:=true] x}>.

Inductive substi (s : tm) (x : string) : tm -> tm -> Prop :=
  | s_var1 :
      substi s x (tm_var x) s
  | s_var2 :
      forall y,
      y <> x ->
      substi s x (tm_var y) (tm_var y)
  | s_abs1 :
      forall T t,
      substi s x <{\x:T, t}> <{\x:T, t}>
  | s_abs2 :
      forall y T t t',
      x <> y ->
      substi s x t t' ->
      substi s x <{\y:T, t}> <{\y:T, t' }>
  | s_app :
      forall t1 t2 t1' t2',
      substi s x t1 t1' ->
      substi s x t2 t2' ->
      substi s x <{ t1 t2 }> <{ t1' t2' }>
  | s_true :
    substi s x <{ true }> <{ true }>
  |   s_false :
      substi s x <{ false }> <{ false }>
  | s_if :
      forall t1 t1' t2 t2' t3 t3',
      substi s x t1 t1' ->
      substi s x t2 t2' ->
      substi s x t3 t3' ->
    substi s x <{ if t1 then t2 else t3 }> <{if t1' then t2' else t3' }>
.

Hint Constructors substi : core.
Theorem substi_correct : forall s x t t',
  <{ [x:=s]t }> = t' <-> substi s x t t'.
Proof.
  intros s x t t'. split. 
  - generalize dependent t'.
    induction t; intros t' H.
    + simpl in H; subst.
      destruct (String.eqb x s0) eqn:Exs0.
      * apply eqb_eq in Exs0; subst; constructor.
      * apply eqb_neq in Exs0. apply s_var2. auto.
    + simpl in H; subst.
      
      
    
