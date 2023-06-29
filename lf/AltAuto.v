(** * AltAuto: A Streamlined Treatment of Automation *)

(** It's time to shorten our proofs through automation
    features:

    - Tacticals

    - Tactics that obviate hardcoded names

    - Automatic solvers

    - Proof search with [auto]

    - Ltac *)

    Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
    From Coq Require Import Arith List.
    From LF Require Import IndProp.
    
    (** Here's a function that rewrites regular expressions into
        potentially simpler forms without changing their matching
        behavior. *)
    
    Fixpoint re_opt_e {T:Type} (re: reg_exp T) : reg_exp T :=
      match re with
      | App EmptyStr re2 => re_opt_e re2
      | App re1 re2 => App (re_opt_e re1) (re_opt_e re2)
      | Union re1 re2 => Union (re_opt_e re1) (re_opt_e re2)
      | Star re => Star (re_opt_e re)
      | _ => re
      end.
    
    (** We would like to show the equivalence of re's with their
        "optimized" form.  One direction of this equivalence looks like
        this (the other is similar).  *)
    
    Lemma re_opt_e_match : forall T (re: reg_exp T) s,
      s =~ re -> s =~ re_opt_e re.
    Proof.
      intros T re s M.
      induction M
        as [| x'
            | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
            | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
            | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
      - (* MEmpty *) simpl. apply MEmpty.
      - (* MChar *) simpl. apply MChar.
      - (* MApp *) simpl.
        destruct re1.
        + apply MApp.
          * apply IH1.
          * apply IH2.
        + inversion Hmatch1. simpl. apply IH2.
        + apply MApp.
          * apply IH1.
          * apply IH2.
        + apply MApp.
          * apply IH1.
          * apply IH2.
        + apply MApp.
          * apply IH1.
          * apply IH2.
        + apply MApp.
          * apply IH1.
          * apply IH2.
      - (* MUnionL *) simpl. apply MUnionL. apply IH.
      - (* MUnionR *) simpl. apply MUnionR. apply IH.
      - (* MStar0 *) simpl. apply MStar0.
      - (* MStarApp *) simpl. apply MStarApp.
        * apply IH1.
        * apply IH2.
    Qed.
    
    (** That last proof was getting a little repetitive.  Time to
        learn a few more Coq tricks... *)
    
    (* ################################################################# *)
    (** * Tacticals *)
    
    (** _Tacticals_ are tactics that take other tactics as arguments --
        "higher-order tactics," if you will.  *)
    
    (* ================================================================= *)
    (** ** The [try] Tactical *)
    
    (** If [T] is a tactic, then [try T] is a tactic that is just like [T]
        except that, if [T] fails, [try T] _successfully_ does nothing at
        all instead of failing. *)
    
    Theorem silly1 : forall n, 1 + n = S n.
    Proof. try reflexivity. (* this just does [reflexivity] *) Qed.
    
    Theorem silly2 : forall (P : Prop), P -> P.
    Proof.
      intros P HP.
      Fail reflexivity.
      try reflexivity. (* proof state is unchanged *)
      apply HP.
    Qed.
    
    (* ================================================================= *)
    (** ** The Sequence Tactical [;] (Simple Form) *)
    
    (** In its most common form, the sequence tactical, written with
        semicolon [;], takes two tactics as arguments.  The compound
        tactic [T; T'] first performs [T] and then performs [T'] on _each
        subgoal_ generated by [T]. *)
    
    (** For example: *)
    
    Lemma simple_semi : forall n, (n + 1 =? 0) = false.
    Proof.
      intros n.
      destruct n eqn:E.
        (* Leaves two subgoals, which are discharged identically...  *)
        - (* n=0 *) simpl. reflexivity.
        - (* n=Sn' *) simpl. reflexivity.
    Qed.
    
    (** We can simplify this proof using the [;] tactical: *)
    
    Lemma simple_semi' : forall n, (n + 1 =? 0) = false.
    Proof.
      intros n.
      (* [destruct] the current goal *)
      destruct n;
      (* then [simpl] each resulting subgoal *)
      simpl;
      (* and do [reflexivity] on each resulting subgoal *)
      reflexivity.
    Qed.
    
    (** Or even more tersely, [destruct] can do the [intro], and [simpl]
        can be omitted: *)
    
    Lemma simple_semi'' : forall n, (n + 1 =? 0) = false.
    Proof.
      destruct n; reflexivity.
    Qed.
    
Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) -> b = c.
Proof.
  intros [] []; try reflexivity; simpl; intros H; rewrite H; reflexivity.
Qed.

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p; induction n as [|n'];
  try reflexivity; simpl; rewrite IHn'; reflexivity.
Qed.
  
Fixpoint nonzeros (lst : list nat) :=
  match lst with
  | [] => []
  | 0 :: t => nonzeros t
  | h :: t => h :: nonzeros t
end.

Lemma nonzeros_app : forall lst1 lst2 : list nat,
  nonzeros (lst1 ++ lst2) = (nonzeros lst1) ++ (nonzeros lst2).
Proof.
  intros l1 l2;
  induction l1 as [|h1 t1];
  try simpl;
  try reflexivity;
  destruct h1;
  rewrite IHt1;
  reflexivity.
Qed.
  
    (** Using [try] and [;] together, we can improve the proof about
        regular expression optimization. *)
    
    Lemma re_opt_e_match' : forall T (re: reg_exp T) s,
      s =~ re -> s =~ re_opt_e re.
    Proof.
      intros T re s M.
      induction M
        as [| x'
            | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
            | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
            | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2];
        (* Do the [simpl] for every case here: *)
        simpl.
      - (* MEmpty *) apply MEmpty.
      - (* MChar *) apply MChar.
      - (* MApp *)
        destruct re1;
        (* Most cases follow by the same formula.  Notice that [apply
           MApp] gives two subgoals: [try apply IH1] is run on _both_ of
           them and succeeds on the first but not the second; [apply IH2]
           is then run on this remaining goal. *)
        try (apply MApp; try apply IH1; apply IH2).
        (* The interesting case, on which [try...] does nothing, is when
           [re1 = EmptyStr]. In this case, we have to appeal to the fact
           that [re1] matches only the empty string: *)
        inversion Hmatch1. simpl. apply IH2.
      - (* MUnionL *) apply MUnionL. apply IH.
      - (* MUnionR *) apply MUnionR. apply IH.
      - (* MStar0 *) apply MStar0.
      - (* MStarApp *)  apply MStarApp. apply IH1.  apply IH2.
    Qed.
    
Theorem app_length : forall (X : Type) (lst1 lst2 : list X),
  length (lst1 ++ lst2) = (length lst1) + (length lst2).
Proof.
  intros; induction lst1;
    [reflexivity | simpl; rewrite IHlst1; reflexivity].
Qed.

Theorem app_length' : forall (X : Type) (lst1 lst2 : list X),
  length (lst1 ++ lst2) = (length lst1) + (length lst2).
Proof.
  intros; induction lst1;
    [idtac | simpl; rewrite IHlst1];  reflexivity.
Qed.

Theorem add_assoc' : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof.
  intros n m p; induction n as [|n'];
  [ reflexivity | simpl; rewrite IHn'; reflexivity].
Qed.
    
    (* ================================================================= *)
    (** ** The [repeat] Tactical *)
    
    (** [repeat] repeats until failure or non-progress. *)
    
    Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
    Proof.
      repeat (try (left; reflexivity); right).
    Qed.
    
Theorem ev100: ev 100.
Proof.
  repeat constructor.
Qed.


(* ################################################################# *)
    (** * Tactics that Make Mentioning Names Unnecessary *)
    
    (** Hardcoding of hypothesis names isn't great. *)
    
    Theorem hyp_name : forall (P : Prop), P -> P.
    Proof.
      intros P HP. apply HP.
    Qed.
    
    (* ================================================================= *)
    (** ** The [assumption] tactic *)
    
    (** Nameless is better. *)
    
    Theorem no_hyp_name : forall (P : Prop), P -> P.
    Proof.
      intros. assumption.
    Qed.
    
    (** There's a tradeoff between ease of reading and ease of
        writing/maintaining. Eliminating hardcoded names can help with
        both. *)
    
    (* ================================================================= *)
    (** ** The [contradiction] tactic *)
    
    (** The [contradiction] tactic handles some ad hoc situations where a
        hypothesis contains [False], or two hypotheses derive [False]. *)
    
    Theorem false_assumed : False -> 0 = 1.
    Proof.
      intros H. destruct H.
    Qed.
    
    Theorem false_assumed' : False -> 0 = 1.
    Proof.
      intros. contradiction.
    Qed.
    
    Theorem contras : forall (P : Prop), P -> ~P -> 0 = 1.
    Proof.
      intros P HP HNP. exfalso. apply HNP. apply HP.
    Qed.
    
    Theorem contras' : forall (P : Prop), P -> ~P -> 0 = 1.
    Proof.
      intros. contradiction.
    Qed.
    
    (* ================================================================= *)
    (** ** The [subst] tactic *)
    
    (** The [subst] tactic substitutes away an identifier, replacing
        it everywhere and eliminating it from the context. That helps
        us to avoid naming hypotheses in [rewrite]s. *)
    
    Theorem many_eq : forall (n m o p : nat),
      n = m ->
      o = p ->
      [n; o] = [m; p].
    Proof.
      intros n m o p Hnm Hop. rewrite Hnm. rewrite Hop. reflexivity.
    Qed.
    
    Theorem many_eq' : forall (n m o p : nat),
      n = m ->
      o = p ->
      [n; o] = [m; p].
    Proof.
      intros. subst. reflexivity.
    Qed.
    
    (* ================================================================= *)
    (** ** The [constructor] tactic *)
    
    (** The [constructor] tactic searches for an applicable
        constructor. *)
    
    Example constructor_example: forall (n:nat),
        ev (n + n).
    Proof.
      induction n; simpl.
      - constructor. (* applies ev_0 *)
      - rewrite add_comm. simpl. constructor. (* applies ev_SS *)
        assumption.
    Qed.
    
    (* ################################################################# *)
    (** * Automatic Solvers *)
    
    (** Coq has several special-purpose tactics that can solve
        certain kinds of goals in a completely automated way. These
        tactics are based on sophisticated algorithms developed for
        verification in specific mathematical or logical domains.
    
        Some automatic solvers are _decision procedures_, which are
        algorithms that always terminate, and always give a correct
        answer. Here, that means that they always find a correct proof, or
        correctly determine that the goal is invalid.  Other automatic
        solvers are _incomplete_: they might fail to find a proof of a
        valid goal. *)
    
    (* ================================================================= *)
    (** ** Linear Integer Arithmetic: The [lia] Tactic *)
    
    (** [lia] is a decision procedure for integer linear
        arithmetic. *)
    
    From Coq Require Import Lia.
    
    Theorem lia_succeed1 : forall (n : nat),
      n > 0 -> n * 2 > n.
    Proof. lia. Qed.
    
    Theorem lia_succeed2 : forall (n m : nat),
        n * m = m * n.
    Proof.
      lia. (* solvable though non-linear *)
    Qed.
    
    Theorem lia_fail1 : 0 = 1.
    Proof.
      Fail lia. (* goal is invalid *)
    Abort.
    
    Theorem lia_fail2 : forall (n : nat),
        n >= 1 -> 2 ^ n = 2 * 2 ^ (n - 1).
    Proof.
      Fail lia. (*goal is non-linear, valid, but unsolvable by lia *)
    Abort.
    
    (* ================================================================= *)
    (** ** Equalities: The [congruence] Tactic *)
    
    (** We don't need to know what a function does to prove
        some equalities. *)
    
    Theorem eq_example1 :
      forall (A B C : Type) (f : A -> B) (g : B -> C) (x : A) (y : B),
        y = f x -> g y = g (f x).
    Proof.
      intros. rewrite H. reflexivity.
    Qed.
    
    (** The essential properties of equality are that it is:
    
        - reflexive
    
        - symmetric
    
        - transitive
    
        - a _congruence_: it respects function and predicate
          application. *)
    
    (** The [congruence] tactic is a decision procedure for equality with
        uninterpreted functions and other symbols.  *)
    
    Theorem eq_example1' :
      forall (A B C : Type) (f : A -> B) (g : B -> C) (x : A) (y : B),
        y = f x -> g y = g (f x).
    Proof.
      congruence.
    Qed.
    
    Theorem eq_example2 : forall (n m o p : nat),
        n = m ->
        o = p ->
        (n, o) = (m, p).
    Proof.
      congruence.
    Qed.
    
    Theorem eq_example3 : forall (X : Type) (h : X) (t : list X),
        [] <> h :: t.
    Proof.
      congruence.
    Qed.
    
    (* ================================================================= *)
    (** ** Propositions: The [intuition] Tactic *)
    
    (** [intuition] implements a decision procedure for
        propositional logic, and simplifies what it cannot prove. *)
    
    Theorem intuition_succeed1 : forall (P : Prop),
        P -> P.
    Proof. intuition. Qed.
    
    Theorem intuition_succeed2 : forall (P Q : Prop),
        ~ (P \/ Q) -> ~P /\ ~Q.
    Proof. intuition. Qed.
    
    Theorem intuition_simplify1 : forall (P : Prop),
        ~~P -> P.
    Proof.
      intuition. (* not a constructively valid formula *)
    Abort.
    
    Theorem intuition_simplify2 : forall (x y : nat) (P Q : nat -> Prop),
      x = y /\ (P x -> Q x) /\ P x -> Q y.
    Proof.
      Fail congruence. (* the propositions stump it *)
      intuition. (* the [=] stumps it, but it simplifies the propositions *)
      congruence.
    Qed.
    
    (** [intuition] takes an optional argument. *)
    
    Theorem intuition_simplify2' : forall (x y : nat) (P Q : nat -> Prop),
      x = y /\ (P x -> Q x) /\ P x -> Q y.
    Proof.
      intuition congruence.
    Qed.
    
    (* ################################################################# *)
    (** * Search Tactics *)
    
    (** The automated solvers we just discussed are capable of finding
        proofs in specific domains. Some of them might pay attention to
        local hypotheses, but overall they don't make use of any custom
        lemmas we've proved, or that are provided by libraries that we
        load.
    
        Another kind of automation that Coq provides does just that: the
        [auto] tactic and its variants search for proofs that can be
        assembled out of hypotheses and lemmas. *)
    
    (* ================================================================= *)
    (** ** The [auto] Tactic *)
    
    (** Until this chapter, our proof scripts mostly applied relevant
        hypotheses or lemmas by name, and one at a time. *)
    
    Example auto_example_1 : forall (P Q R: Prop),
      (P -> Q) -> (Q -> R) -> P -> R.
    Proof.
      intros P Q R H1 H2 H3.
      apply H2. apply H1. apply H3.
    Qed.
    
    (** The [auto] tactic frees us from this drudgery by _searching_ for a
        sequence of applications that will prove the goal: *)
    
    Example auto_example_1' : forall (P Q R: Prop),
      (P -> Q) -> (Q -> R) -> P -> R.
    Proof.
      auto.
    Qed.
    
    (** The [auto] tactic solves goals that are solvable by any combination of
         - [intros] and
         - [apply] (of hypotheses from the local context, by default). *)
    
    (** Here is a more interesting example showing [auto]'s power: *)
    
    Example auto_example_2 : forall P Q R S T U : Prop,
      (P -> Q) ->
      (P -> R) ->
      (T -> R) ->
      (S -> T -> U) ->
      ((P -> Q) -> (P -> S)) ->
      T ->
      P ->
      U.
    Proof. auto. Qed.
    
    (** Proof search could, in principle, take an arbitrarily long time,
        so there are limits to how far [auto] will search by default. *)
    
    Example auto_example_3 : forall (P Q R S T U: Prop),
      (P -> Q) ->
      (Q -> R) ->
      (R -> S) ->
      (S -> T) ->
      (T -> U) ->
      P ->
      U.
    Proof.
      (* When it cannot solve the goal, [auto] does nothing *)
      auto.
      (* Optional argument says how deep to search (default is 5) *)
      auto 6.
    Qed.
    
    (** The [auto] tactic considers the hypotheses in the current context
        together with a _hint database_ of other lemmas and constructors.
        Some common facts about equality and logical operators are
        installed in the hint database by default. *)
    
    Example auto_example_4 : forall P Q R : Prop,
      Q ->
      (Q -> R) ->
      P \/ (Q /\ R).
    Proof. auto. Qed.
    
    (** If we want to see which facts [auto] is using, we can use
        [info_auto] instead. *)
    
    Example auto_example_5 : 2 = 2.
    Proof.
      (* [auto] subsumes [reflexivity] because [eq_refl] is in the hint
         database. *)
      info_auto.
    Qed.
    
    (** We can extend the hint database with theorem [t] just for the
        purposes of one application of [auto] by writing [auto using
        t]. *)
    
    Lemma le_antisym : forall n m: nat, (n <= m /\ m <= n) -> n = m.
    Proof. intros. lia. Qed.
    
    Example auto_example_6 : forall n m p : nat,
      (n <= p -> (n <= m /\ m <= n)) ->
      n <= p ->
      n = m.
    Proof.
      auto using le_antisym.
    Qed.
    
    (** We can also extend hint databases for future uses:
    
          - [Hint Resolve T : db.]
    
              Add theorem or constructor [T] to [db].
    
          - [Hint Constructors c : db.]
    
              Add _all_ constructors of [c] to [db].
    
          - [Hint Unfold d : db.]
    
              Automatically expand defined symbol [d] when using [db].
    *)
    
    Create HintDb le_db.
    Hint Resolve le_antisym : le_db.
    
    Example auto_example_6' : forall n m p : nat,
      (n <= p -> (n <= m /\ m <= n)) ->
      n <= p ->
      n = m.
    Proof.
      auto with le_db.
    Qed.
    
    (* ================================================================= *)
    (** ** The [eauto] variant *)
    
    (** Consider this example: *)
    
    Example trans_example1:  forall a b c d,
        a <= b + b * c  ->
        (1 + c) * b <= d ->
        a <= d.
    Proof.
      intros a b c d H1 H2.
      apply le_trans with (b + b * c).
        (* ^ We must supply the intermediate value *)
      - apply H1.
      - simpl in H2. rewrite mul_comm. apply H2.
    Qed.
    
    (** [apply] fails if we leave out the [with], even though the
        appropriate value for [n] will become obvious in the very next
        step. *)
    
    (** With [eapply], we can eliminate this silliness: *)
    
    Example trans_example1':  forall a b c d,
        a <= b + b * c  ->
        (1 + c) * b <= d ->
        a <= d.
    Proof.
      intros a b c d H1 H2.
      eapply le_trans. (* 1 *)
      - apply H1. (* 2 *)
      - simpl in H2. rewrite mul_comm. apply H2.
    Qed.
    
    (** Again, using [eauto]. *)
    
    Example trans_example2:  forall a b c d,
        a <= b + b * c  ->
        b + b * c <= d ->
        a <= d.
    Proof.
      intros a b c d H1 H2.
      info_eauto using le_trans.
    Qed.
    
    (** [eauto] is significantly slower than [auto]. Use only as
        needed. *)
    
    (* ################################################################# *)
    (** * Ltac: The Tactic Language *)
    
    (** New tactics can be defined in two ways:
    
        - OCaml: low-level implementation (for wizards)
    
        - Ltac: in-Coq language (for everyone) *)
    
    (* ================================================================= *)
    (** ** Ltac Functions *)
    
    (** Here is a simple [Ltac] example: *)
    
    Ltac simpl_and_try tac := simpl; try tac.
    
    Example sat_ex1 : 1 + 1 = 2.
    Proof. simpl_and_try reflexivity. Qed.
    
    Example sat_ex2 : forall (n : nat), 1 - 1 + n + 1 = 1 + n.
    Proof. simpl_and_try reflexivity. lia. Qed.
    
    (** For a more useful tactic, consider these three proofs from
        [Basics], and how structurally similar they all are: *)
    
    Theorem plus_1_neq_0 : forall n : nat,
      (n + 1) =? 0 = false.
    Proof.
      intros n. destruct n.
      - reflexivity.
      - reflexivity.
    Qed.
    
    Theorem negb_involutive : forall b : bool,
      negb (negb b) = b.
    Proof.
      intros b. destruct b.
      - reflexivity.
      - reflexivity.
    Qed.
    
    Theorem andb_commutative : forall b c, andb b c = andb c b.
    Proof.
      intros b c. destruct b.
      - destruct c.
        + reflexivity.
        + reflexivity.
      - destruct c.
        + reflexivity.
        + reflexivity.
    Qed.
    
    (** We can factor out the common structure:
    
        - Do a destruct.
    
        - For each branch, finish with [reflexivity] -- if possible. *)
    
    Ltac destructpf x :=
      destruct x; try reflexivity.
    
    Theorem plus_1_neq_0' : forall n : nat,
        (n + 1) =? 0 = false.
    Proof. intros n; destructpf n. Qed.
    
    Theorem negb_involutive' : forall b : bool,
      negb (negb b) = b.
    Proof. intros b; destructpf b. Qed.
    
    Theorem andb_commutative' : forall b c, andb b c = andb c b.
    Proof.
      intros b c; destructpf b; destructpf c.
    Qed.
    
    (* ================================================================= *)
    (** ** Ltac Pattern Matching *)
    
    (** Here is another common proof pattern that we have seen in
        many simple proofs by induction: *)
    
    Theorem app_nil_r : forall (X : Type) (lst : list X),
        lst ++ [] = lst.
    Proof.
      intros X lst. induction lst as [ | h t IHt].
      - reflexivity.
      - simpl. rewrite IHt. reflexivity.
    Qed.
    
    (** How can we automate that pattern? Ltac has a [match goal]
        tactic. *)
    
    Theorem match_ex1 : True.
    Proof.
      match goal with
      | [ |- True ] => apply I
      end.
    Qed.
    
    (** That says: if the conclusion is [True] (regardless of the
        hypotheses), run [apply I]. *)
    
    (** There may be multiple branches, which are tried in order. *)
    
    Theorem match_ex2 : True /\ True.
    Proof.
      match goal with
      | [ |- True ] => apply I
      | [ |- True /\ True ] => split; apply I
      end.
    Qed.
    
    (** To see what branches are being tried, it can help to insert calls
        to the identity tactic [idtac]. It optionally accepts an argument
        to print out as debugging information. *)
    
    Theorem match_ex2' : True /\ True.
    Proof.
      match goal with
      | [ |- True ] => idtac "branch 1"; apply I
      | [ |- True /\ True ] => idtac "branch 2"; split; apply I
      end.
    Qed.
    
    (** Only the second branch was tried. The first one did not match the
        goal. *)
    
    (** Ordinary [match] doesn't allow redundant branches. *)
    
    Fail Definition redundant_match (n : nat) : nat :=
      match n with
      | x => x
      | 0 => 1
      end.
    
    (** But [match goal] keeps trying until success. *)
    
    Theorem match_ex2'' : True /\ True.
    Proof.
      match goal with
      | [ |- _ ] => idtac "branch 1"; apply I
      | [ |- True /\ True ] => idtac "branch 2"; split; apply I
      end.
    Qed.
    
    Theorem match_ex2''' : True /\ True.
    Proof.
      Fail match goal with
      | [ |- _ ] => idtac "branch 1"; apply I
      | [ |- _ ] => idtac "branch 2"; apply I
      end.
    Abort.
    
    (** A match against a hypothesis: *)
    
    Theorem match_ex3 : forall (P : Prop), P -> P.
    Proof.
      intros P HP.
      match goal with
      | [ H : _ |- _ ] => apply H
      end.
    Qed.
    
    (** [H] is bound to [HP], as shown by printout from [idtac
        H]. *)
    
    Theorem match_ex3' : forall (P : Prop), P -> P.
    Proof.
      intros P HP.
      match goal with
      | [ H : _ |- _ ] => idtac H; apply H
      end.
    Qed.
    
    (** Matching will _backtrack_ and retry with other
        hypotheses as necessary. *)
    
    Theorem match_ex4 : forall (P Q : Prop), P -> Q -> P.
    Proof.
      intros P Q HP HQ.
      match goal with
      | [ H : _ |- _ ] => idtac H; apply H
      end.
    Qed.
    
    (** But if there were no successful hypotheses, the entire match
        would fail: *)
    
    Theorem match_ex5 : forall (P Q R : Prop), P -> Q -> R.
    Proof.
      intros P Q R HP HQ.
      Fail match goal with
      | [ H : _ |- _ ] => idtac H; apply H
      end.
    Abort.
    
    (** _Metavariables_ are pattern variables for the goal: *)
    
    Theorem match_ex5 : forall (P Q : Prop), P -> Q -> P.
    Proof.
      intros P Q HP HQ.
      match goal with
      | [ H : ?X |- ?X ] => idtac H; apply H
      end.
    Qed.
    
    (** That applies only [HP], because [HQ] doesn't match. *)
    
    (** With [match] against terms, pattern variables can't be
        repeated: *)
    
    Fail Definition dup_first_two_elts (lst : list nat) :=
      match lst with
      | x :: x :: _ => true
      | _ => false
      end.
    
    (** The technical term for this is _linearity_: regular [match]
        requires pattern variables to be _linear_, meaning that they are
        used only once. Tactic [match goal] permits _non-linear_
        metavariables, meaning that they can be used multiple times in a
        pattern and must bind the same term each time. *)
    
    (** Now that we've learned a bit about [match goal], let's return
        to the proof pattern of some simple inductions: *)
    
    Theorem app_nil_r' : forall (X : Type) (lst : list X),
        lst ++ [] = lst.
    Proof.
      intros X lst. induction lst as [ | h t IHt].
      - reflexivity.
      - simpl. rewrite IHt. reflexivity.
    Qed.
    
    (** With [match goal], we can automate that proof pattern: *)
    
    Ltac simple_induction t :=
      induction t; simpl;
      try match goal with
          | [H : _ = _ |- _] => rewrite H
          end;
      reflexivity.
    
    Theorem app_nil_r'' : forall (X : Type) (lst : list X),
        lst ++ [] = lst.
    Proof.
      intros X lst. simple_induction lst.
    Qed.
    
    (** That works great! Here are two other proofs that follow the same
        pattern. *)
    
    Theorem add_assoc'' : forall n m p : nat,
        n + (m + p) = (n + m) + p.
    Proof.
      intros n m p. induction n.
      - reflexivity.
      - simpl. rewrite IHn. reflexivity.
    Qed.
    
    Theorem add_assoc''' : forall n m p : nat,
        n + (m + p) = (n + m) + p.
    Proof.
      intros n m p. simple_induction n.
    Qed.
    
    Theorem plus_n_Sm : forall n m : nat,
        S (n + m) = n + (S m).
    Proof.
      intros n m. induction n.
      - reflexivity.
      - simpl. rewrite IHn. reflexivity.
    Qed.
    
    Theorem plus_n_Sm' : forall n m : nat,
        S (n + m) = n + (S m).
    Proof.
      intros n m. simple_induction n.
    Qed.
    
    (* ################################################################# *)
    (** * Review *)
    
    (** We've learned a lot of new features and tactics in this chapter:
    
        - [try], [;], [repeat]
    
        - [assumption], [contradiction], [subst], [constructor]
    
        - [lia], [congruence], [intuition]
    
        - [auto], [eauto], [eapply]
    
        - Ltac functions and [match goal] *)
    