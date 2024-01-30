Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From PLF Require Import Smallstep.
From PLF Require Import Stlc.

Module STLCExtendedRecords.

Module FirstTry.
Definition alist (X : Type) := list (string * X).
Inductive ty : Type :=
  | Base : string -> ty
  | Arrow : ty -> ty -> ty
  | TRcd : (alist ty) -> ty.
  
Check ty_ind.

End FirstTry.

Inductive ty : Type :=
  | Ty_Base : string -> ty
  | Ty_Arrow : ty -> ty -> ty
  | Ty_RNil : ty
  | Ty_RCons : string -> ty -> ty -> ty.
  
Inductive tm : Type :=
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  (* records *)
  | tm_rproj : tm -> string -> tm
  | tm_rnil : tm
  | tm_rcons : string -> tm -> tm -> tm.
  
Declare Custom Entry stlc_ty.
Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "<{{ e }}>" := e (e custom stlc_ty at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "( x )" := x (in custom stlc_ty, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "x" := x (in custom stlc_ty at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc_ty at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc at level 90, x at level 99,
                     t custom stlc_ty at level 99,
                     y custom stlc at level 99,
                     left associativity).
Coercion tm_var : string >-> tm.
Notation "{ x }" := x (in custom stlc at level 1, x constr).
Notation "'Base' x" := (Ty_Base x) (in custom stlc_ty at level 0).
Notation " l ':' t1 '::' t2" := (Ty_RCons l t1 t2) (in custom stlc_ty at level 3, right associativity).
Notation " l := e1 '::' e2" := (tm_rcons l e1 e2) (in custom stlc at level 3, right associativity).
Notation "'nil'" := (Ty_RNil) (in custom stlc_ty).
Notation "'nil'" := (tm_rnil) (in custom stlc).
Notation "o --> l" := (tm_rproj o l) (in custom stlc at level 0).

Open Scope string_scope.
Notation a := "a".
Notation f := "f".
Notation g := "g".
Notation l := "l".
Notation A := <{{ Base "A" }}>.
Notation B := <{{ Base "B" }}>.
Notation k := "k".
Notation i1 := "i1".
Notation i2 := "i2".

Definition weird_type := <{{ a : A :: B }}>.

Inductive record_ty : ty -> Prop :=
  | RTnil :
        record_ty <{{ nil }}>
  | RTcons : forall i T1 T2,
        record_ty <{{ i : T1 :: T2 }}>.

Inductive well_formed_ty : ty -> Prop :=
  | wfBase : forall (i : string),
        well_formed_ty <{{ Base i }}>
  | wfArrow : forall T1 T2,
        well_formed_ty T1 ->
        well_formed_ty T2 ->
        well_formed_ty <{{ T1 -> T2 }}>
  | wfRNil :
        well_formed_ty <{{ nil }}>
  | wfRCons : forall i T1 T2,
        well_formed_ty T1 ->
        well_formed_ty T2 ->
        record_ty T2 ->
        well_formed_ty <{{ i : T1 :: T2 }}>.
Hint Constructors record_ty well_formed_ty : core.

Inductive record_tm : tm -> Prop :=
  | rtnil :
        record_tm <{ nil }>
  | rtcons : forall i t1 t2,
        record_tm <{ i := t1 :: t2 }>.
Hint Constructors record_tm : core.

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).
Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if String.eqb x y then s else t
  | <{\y:T, t1}> =>
      if String.eqb x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
  | <{ t1 --> i }> =>
      <{ ( [x := s] t1) --> i }>
  | <{ nil }> =>
      <{ nil }>
  | <{ i := t1 :: tr }> =>
     <{ i := [x := s] t1 :: ( [x := s] tr) }>
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{ \ x : T2, t1 }>
  | v_rnil : value <{ nil }>
  | v_rcons : forall i v1 vr,
      value v1 ->
      value vr ->
      value <{ i := v1 :: vr }>.
Hint Constructors value : core.

Fixpoint tlookup (i:string) (tr:tm) : option tm :=
  match tr with
  | <{ i' := t :: tr'}> => if String.eqb i i' then Some t else tlookup i tr'
  | _ => None
  end.
  
Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T2 t1 v2,
         value v2 ->
         <{(\x:T2, t1) v2}> --> <{ [x:=v2]t1 }>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1 t2'}>
  | ST_Proj1 : forall t1 t1' i,
        t1 --> t1' ->
        <{ t1 --> i }> --> <{ t1' --> i }>
  | ST_ProjRcd : forall tr i vi,
        value tr ->
        tlookup i tr = Some vi ->
        <{ tr --> i }> --> vi
  | ST_Rcd_Head : forall i t1 t1' tr2,
        t1 --> t1' ->
        <{ i := t1 :: tr2 }> --> <{ i := t1' :: tr2 }>
  | ST_Rcd_Tail : forall i v1 tr2 tr2',
        value v1 ->
        tr2 --> tr2' ->
        <{ i := v1 :: tr2 }> --> <{ i := v1 :: tr2' }>

where "t '-->' t'" := (step t t').
Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).
Hint Constructors step : core.

Fixpoint Tlookup (i:string) (Tr:ty) : option ty :=
  match Tr with
  | <{{ i' : T :: Tr' }}> =>
      if String.eqb i i' then Some T else Tlookup i Tr'
  | _ => None
  end.
Definition context := partial_map ty.

Reserved Notation "Gamma '|--' t '\in' T" (at level 40, t custom stlc, T custom stlc_ty at level 0).

Inductive has_type (Gamma : context) : tm -> ty -> Prop :=
  | T_Var : forall x T,
      Gamma x = Some T ->
      well_formed_ty T ->
      Gamma |-- x \in T
  | T_Abs : forall x T11 T12 t12,
      well_formed_ty T11 ->
      (x |-> T11; Gamma) |-- t12 \in T12 ->
      Gamma |-- \x : T11, t12 \in (T11 -> T12)
  | T_App : forall T1 T2 t1 t2,
      Gamma |-- t1 \in (T1 -> T2) ->
      Gamma |-- t2 \in T1 ->
      Gamma |-- ( t1 t2) \in T2
  (* records: *)
  | T_Proj : forall i t Ti Tr,
      Gamma |-- t \in Tr ->
      Tlookup i Tr = Some Ti ->
      Gamma |-- (t --> i) \in Ti
  | T_RNil :
      Gamma |-- nil \in nil
  | T_RCons : forall i t T tr Tr,
      Gamma |-- t \in T ->
      Gamma |-- tr \in Tr ->
      record_ty Tr ->
      record_tm tr ->
      Gamma |-- ( i := t :: tr) \in ( i : T :: Tr)

where "Gamma '|--' t '\in' T" := (has_type Gamma t T).
Hint Constructors has_type : core.

Lemma typing_example_2 :
  empty |-- (\a : ( i1 : (A -> A) :: i2 : (B -> B) :: nil), a --> i2)
            ( i1 := (\a : A, a) :: i2 := (\a : B,a ) :: nil ) \in (B -> B).
Proof.
  eapply T_App.
  - constructor. constructor; auto. eapply T_Proj.
    + constructor. unfold update. reflexivity. auto.
    + simpl. reflexivity.
  - constructor; auto.
Qed.

Example typing_nonexample :
  ~ exists T,
     (a |-> <{{ i2 : (A -> A) :: nil }}>) |--
       ( i1 := (\a : B, a) :: a ) \in
               T.
Proof.
  intro.
  destruct H.
  inversion H; subst; clear H.
  inversion H7.
Qed.
Example typing_nonexample_2 : forall y,
  ~ exists T,
    (y |-> A) |--
     (\a : ( i1 : A :: nil ), a --> i1 )
      ( i1 := y :: i2 := y :: nil ) \in T.
Proof.
  intros y Hcontra.
  inversion Hcontra; clear Hcontra.

  inversion H; subst; clear H.

  (* find out the T1 in T1 -> x *)
  inversion H2; subst; clear H2.
  inversion H7; subst; clear H7.
  simpl in H5.
  inversion H2; subst; clear H2.
  unfold update in *; rewrite t_update_eq in H0.
  inversion H0; subst; clear H0.
  simpl in H5. inversion H5; subst; clear H5.
  clear H1 H3.

