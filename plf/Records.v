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