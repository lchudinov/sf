Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From PLF Require Import Smallstep.
Module RecordSub.

Inductive ty : Type :=
  (* proper types *)
  | Ty_Top : ty
  | Ty_Base : string -> ty
  | Ty_Arrow : ty -> ty -> ty
  (* record types *)
  | Ty_RNil : ty
  | Ty_RCons : string -> ty -> ty -> ty.
Inductive tm : Type :=
  (* proper terms *)
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  | tm_rproj : tm -> string -> tm
  (* record terms *)
  | tm_rnil : tm
  | tm_rcons : string -> tm -> tm -> tm.
Declare Custom Entry stlc.
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
Notation "'Top'" := (Ty_Top) (in custom stlc_ty at level 0).

Inductive record_ty : ty -> Prop :=
  | RTnil :
        record_ty <{{ nil }}>
  | RTcons : forall i T1 T2,
        record_ty <{{ i : T1 :: T2 }}>.
Inductive record_tm : tm -> Prop :=
  | rtnil :
        record_tm <{ nil }>
  | rtcons : forall i t1 t2,
        record_tm <{ i := t1 :: t2 }>.
Inductive well_formed_ty : ty -> Prop :=
  | wfTop :
        well_formed_ty <{{ Top }}>
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
Hint Constructors record_ty record_tm well_formed_ty : core.

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

Fixpoint Tlookup (i:string) (Tr:ty) : option ty :=
  match Tr with
  | <{{ i' : T :: Tr' }}> =>
      if String.eqb i i' then Some T else Tlookup i Tr'
  | _ => None
  end.

Fixpoint tlookup (i:string) (tr:tm) : option tm :=
  match tr with
  | <{ i' := t :: tr' }> =>
      if String.eqb i i' then Some t else tlookup i tr'
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
Hint Constructors step : core.

Reserved Notation "T '<:' U" (at level 40).

Inductive subtype : ty -> ty -> Prop :=
  (* Subtyping between proper types *)
  | S_Refl : forall T,
    well_formed_ty T ->
    T <: T
  | S_Trans : forall S U T,
    S <: U ->
    U <: T ->
    S <: T
  | S_Top : forall S,
    well_formed_ty S ->
    S <: <{{ Top }}>
  | S_Arrow : forall S1 S2 T1 T2,
    T1 <: S1 ->
    S2 <: T2 ->
    <{{ S1 -> S2 }}> <: <{{ T1 -> T2 }}>
  (* Subtyping between record types *)
  | S_RcdWidth : forall i T1 T2,
    well_formed_ty <{{ i : T1 :: T2 }}> ->
    <{{ i : T1 :: T2 }}> <: <{{ nil }}>
  | S_RcdDepth : forall i S1 T1 Sr2 Tr2,
    S1 <: T1 ->
    Sr2 <: Tr2 ->
    record_ty Sr2 ->
    record_ty Tr2 ->
    <{{ i : S1 :: Sr2 }}> <: <{{ i : T1 :: Tr2 }}>
  | S_RcdPerm : forall i1 i2 T1 T2 Tr3,
    well_formed_ty <{{ i1 : T1 :: i2 : T2 :: Tr3 }}> ->
    i1 <> i2 ->
       <{{ i1 : T1 :: i2 : T2 :: Tr3 }}>
    <: <{{ i2 : T2 :: i1 : T1 :: Tr3 }}>

where "T '<:' U" := (subtype T U).

Hint Constructors subtype : core.


Module Examples.
Open Scope string_scope.
Notation x := "x".
Notation y := "y".
Notation z := "z".
Notation j := "j".
Notation k := "k".
Notation i := "i".
Notation A := <{{ Base "A" }}>.
Notation B := <{{ Base "B" }}>.
Notation C := <{{ Base "C" }}>.
Definition TRcd_j :=
  <{{ j : (B -> B) :: nil }}>. (* {j:B->B} *)
Definition TRcd_kj :=
  <{{ k : (A -> A) :: TRcd_j }}>. (* {k:C->C,j:B->B} *)
Example subtyping_example_0 :
  <{{ C -> TRcd_kj }}> <: <{{ C -> nil }}>.
Proof.
  apply S_Arrow.
    apply S_Refl. auto.
    unfold TRcd_kj, TRcd_j. apply S_RcdWidth; auto.
Qed.

Example subtyping_example_1 :
  TRcd_kj <: TRcd_j.
(* {k:A->A,j:B->B} <: {j:B->B} *)
Proof with eauto.
  unfold TRcd_kj, TRcd_j.
  eapply S_Trans.
  apply S_RcdPerm...
  - intros contra. inversion contra.
  - apply S_RcdDepth...
Qed.
Example subtyping_example_2 :
  <{{ Top -> TRcd_kj }}> <:
          <{{ (C -> C) -> TRcd_j }}>.
Proof with eauto.
  unfold TRcd_kj, TRcd_j.
  apply S_Arrow...
  apply subtyping_example_1.
Qed.

Example subtyping_example_3 :
  <{{ nil -> (j : A :: nil) }}> <:
          <{{ (k : B :: nil) -> nil }}>.
(* {}->{j:A} <: {k:B}->{} *)
Proof with eauto.
  apply S_Arrow...
Qed.

Example subtyping_example_4 :
  <{{ x : A :: y : B :: z : C :: nil }}> <:
  <{{ z : C :: y : B :: x : A :: nil }}>.
Proof with eauto.
  Admitted.
End Examples.

Lemma subtype__wf : forall S T,
  subtype S T ->
  well_formed_ty T /\ well_formed_ty S.
Proof with eauto.
  intros S T Hsub.
  induction Hsub;
    intros; try (destruct IHHsub1; destruct IHHsub2)...
  - (* S_RcdPerm *)
    split... inversion H. subst. inversion H5... Qed.

Lemma wf_rcd_lookup : forall i T Ti,
  well_formed_ty T ->
  Tlookup i T = Some Ti ->
  well_formed_ty Ti.
Proof with eauto.
  intros i T.
  induction T; intros; try solve_by_invert.
  - (* RCons *)
    inversion H. subst. unfold Tlookup in H0.
    destruct (String.eqb i s)... inversion H0; subst...
Qed.

Lemma rcd_types_match : forall S T i Ti,
  subtype S T ->
  Tlookup i T = Some Ti ->
  exists Si, Tlookup i S = Some Si /\ subtype Si Ti.
Proof with (eauto using wf_rcd_lookup).
  intros S T i Ti Hsub Hget. generalize dependent Ti.
  induction Hsub; intros Ti Hget;
    try solve_by_invert.
  - (* S_Refl *)
    exists Ti...
  - (* S_Trans *)
    destruct (IHHsub2 Ti) as [Ui Hui]... destruct Hui.
    destruct (IHHsub1 Ui) as [Si Hsi]... destruct Hsi.
    exists Si...
  - (* S_RcdDepth *)
    rename i0 into k.
    unfold Tlookup. unfold Tlookup in Hget.
    destruct (String.eqb i k)...
    + (* i = k -- we're looking up the first field *)
      inversion Hget. subst. exists S1...
  - (* S_RcdPerm *)
    exists Ti. split.
    + (* lookup *)
      unfold Tlookup. unfold Tlookup in Hget.
      destruct (eqb_spec i i1)...
      * (* i = i1 -- we're looking up the first field *)
        destruct (eqb_spec i i2)...
        (* i = i2 -- contradictory *)
        destruct H0.
        subst...
    + (* subtype *)
      inversion H. subst. inversion H5. subst...
Qed.

Lemma sub_inversion_arrow : forall U V1 V2,
     U <: <{{ V1 -> V2 }}> ->
     exists U1 U2,
       (U= <{{ U1 -> U2 }}> ) /\ (V1 <: U1) /\ (U2 <: V2).
Proof with eauto.
  intros U V1 V2 Hs.
  remember <{{ V1 -> V2 }}> as V.
  generalize dependent V2. generalize dependent V1.
  induction Hs; intros; try solve_by_invert.
  - subst. inversion H. exists V1, V2...
  - apply IHHs2 in HeqV. destruct HeqV as [X1 [X2 [H4 [H5 H6]]]].
    exists X1, X2...
Admitted.

Definition context := partial_map ty.

Reserved Notation "Gamma '|--' t '\in' T" (at level 40,
                                          t custom stlc at level 99, T custom stlc_ty at level 0).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma (x : string) T,
      Gamma x = Some T ->
      well_formed_ty T -> 
      Gamma |-- x \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      well_formed_ty T11 ->
      (x |-> T11; Gamma) |-- t12 \in T12 ->
      Gamma |-- (\ x : T11, t12) \in (T11 -> T12)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |-- t1 \in (T1 -> T2) ->
      Gamma |-- t2 \in T1 ->
      Gamma |-- t1 t2 \in T2
  | T_Proj : forall Gamma i t T Ti,
      Gamma |-- t \in T ->
      Tlookup i T = Some Ti ->
      Gamma |-- t --> i \in Ti
  (* Subsumption *)
  | T_Sub : forall Gamma t S T,
      Gamma |-- t \in S ->
      subtype S T ->
      Gamma |-- t \in T
  (* Rules for record terms *)
  | T_RNil : forall Gamma,
      Gamma |-- nil \in nil
  | T_RCons : forall Gamma i t T tr Tr,
      Gamma |-- t \in T ->
      Gamma |-- tr \in Tr ->
      record_ty Tr ->
      record_tm tr ->
      Gamma |-- i := t :: tr \in (i : T :: Tr)

where "Gamma '|--' t '\in' T" := (has_type Gamma t T).
Hint Constructors has_type : core.

Module Examples2.
Import Examples.

Definition trcd_kj :=
  <{ k := (\z : A, z) :: j := (\z : B, z) :: nil }>.
Example typing_example_0 :
  empty |-- trcd_kj \in TRcd_kj.
(* empty |-- {k=(\z:A.z), j=(\z:B.z)} : {k:A->A,j:B->B} *)
Proof.
  unfold trcd_kj, TRcd_kj, TRcd_j.
  eapply T_RCons; try auto.
Qed.

Example typing_example_1 :
  empty |-- (\x : TRcd_j, x --> j) trcd_kj \in (B -> B).
(* empty |-- (\x:{k:A->A,j:B->B}, x.j)
              {k=(\z:A,z), j=(\z:B,z)}
         : B->B *)
Proof with eauto.
  unfold trcd_kj, TRcd_kj, TRcd_j.
  eapply T_App.
  - 

  (* FILL IN HERE *) Admitted.