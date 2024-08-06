Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

(** Roger: changed CoqLNOutput.hs to include -notation-overridden
 and put before HdmDefs import *)

Local Set Warnings "-non-recursive,-deprecated-tactic,-notation-overridden,-intuition-auto-with-star". 

Require Import Metalib.Metatheory.
Require Import Metalib.LibLNgen.

Require Import Defs.HdmLemsDeps.

(** NOTE: Auxiliary theorems are hidden in generated documentation.
    In general, there is a [_rec] version of every lemma involving
    [open] and [close]. *)


(* *********************************************************************** *)
(** * Induction principles for nonterminals *)

Scheme Ex_ind' := Induction for Ex Sort Prop.

Combined Scheme Ex_mutind from Ex_ind'.

Scheme Ex_rec' := Induction for Ex Sort Set.

Combined Scheme Ex_mutrec from Ex_rec'.

Scheme T_ind' := Induction for T Sort Prop.

Combined Scheme T_mutind from T_ind'.

Scheme T_rec' := Induction for T Sort Set.

Combined Scheme T_mutrec from T_rec'.

Scheme Sc_ind' := Induction for Sc Sort Prop.

Combined Scheme Sc_mutind from Sc_ind'.

Scheme Sc_rec' := Induction for Sc Sort Set.

Combined Scheme Sc_mutrec from Sc_rec'.

Scheme Tm_ind' := Induction for Tm Sort Prop.

Combined Scheme Tm_mutind from Tm_ind'.

Scheme Tm_rec' := Induction for Tm Sort Set.

Combined Scheme Tm_mutrec from Tm_rec'.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_Ex (e1 : Ex) {struct e1} : nat :=
  match e1 with
    | e__Var_f x1 => 1
    | e__Var_b n1 => 1
    | e__Unit => 1
    | e__App e2 e3 => 1 + (size_Ex e2) + (size_Ex e3)
    | e__Lam e2 => 1 + (size_Ex e2)
    | e__Let e2 e3 => 1 + (size_Ex e2) + (size_Ex e3)
  end.

Fixpoint size_T (T1 : T) {struct T1} : nat :=
  match T1 with
    | T__Var_f alpha1 => 1
    | T__Var_b n1 => 1
    | T__Unit => 1
    | T__Bool => 1
    | T__Fun tau1 tau2 => 1 + (size_T tau1) + (size_T tau2)
  end.

Fixpoint size_Sc (Sc1 : Sc) {struct Sc1} : nat :=
  match Sc1 with
    | S__T tau1 => 1 + (size_T tau1)
    | S__Forall sigma1 => 1 + (size_Sc sigma1)
  end.

Fixpoint size_Tm (t1 : Tm) {struct t1} : nat :=
  match t1 with
    | t__Var_f tx1 => 1
    | t__Var_b n1 => 1
    | t__Unit => 1
    | t__True => 1
    | t__False => 1
    | t__App t2 t3 => 1 + (size_Tm t2) + (size_Tm t3)
    | t__TApp t2 tau1 => 1 + (size_Tm t2) + (size_T tau1)
    | t__Lam tau1 t2 => 1 + (size_T tau1) + (size_Tm t2)
    | t__TLam t2 => 1 + (size_Tm t2)
  end.


(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_Ex_wrt_Ex : nat -> Ex -> Prop :=
  | degree_wrt_Ex_e__Var_f : forall n1 x1,
    degree_Ex_wrt_Ex n1 (e__Var_f x1)
  | degree_wrt_Ex_e__Var_b : forall n1 n2,
    lt n2 n1 ->
    degree_Ex_wrt_Ex n1 (e__Var_b n2)
  | degree_wrt_Ex_e__Unit : forall n1,
    degree_Ex_wrt_Ex n1 (e__Unit)
  | degree_wrt_Ex_e__App : forall n1 e1 e2,
    degree_Ex_wrt_Ex n1 e1 ->
    degree_Ex_wrt_Ex n1 e2 ->
    degree_Ex_wrt_Ex n1 (e__App e1 e2)
  | degree_wrt_Ex_e__Lam : forall n1 e1,
    degree_Ex_wrt_Ex (S n1) e1 ->
    degree_Ex_wrt_Ex n1 (e__Lam e1)
  | degree_wrt_Ex_e__Let : forall n1 e1 e2,
    degree_Ex_wrt_Ex n1 e1 ->
    degree_Ex_wrt_Ex (S n1) e2 ->
    degree_Ex_wrt_Ex n1 (e__Let e1 e2).

Scheme degree_Ex_wrt_Ex_ind' := Induction for degree_Ex_wrt_Ex Sort Prop.

Combined Scheme degree_Ex_wrt_Ex_mutind from degree_Ex_wrt_Ex_ind'.

#[export] Hint Constructors degree_Ex_wrt_Ex : core lngen.

Inductive degree_T_wrt_T : nat -> T -> Prop :=
  | degree_wrt_T_T__Var_f : forall n1 alpha1,
    degree_T_wrt_T n1 (T__Var_f alpha1)
  | degree_wrt_T_T__Var_b : forall n1 n2,
    lt n2 n1 ->
    degree_T_wrt_T n1 (T__Var_b n2)
  | degree_wrt_T_T__Unit : forall n1,
    degree_T_wrt_T n1 (T__Unit)
  | degree_wrt_T_T__Bool : forall n1,
    degree_T_wrt_T n1 (T__Bool)
  | degree_wrt_T_T__Fun : forall n1 tau1 tau2,
    degree_T_wrt_T n1 tau1 ->
    degree_T_wrt_T n1 tau2 ->
    degree_T_wrt_T n1 (T__Fun tau1 tau2).

Scheme degree_T_wrt_T_ind' := Induction for degree_T_wrt_T Sort Prop.

Combined Scheme degree_T_wrt_T_mutind from degree_T_wrt_T_ind'.

#[export] Hint Constructors degree_T_wrt_T : core lngen.

Inductive degree_Sc_wrt_T : nat -> Sc -> Prop :=
  | degree_wrt_T_S__T : forall n1 tau1,
    degree_T_wrt_T n1 tau1 ->
    degree_Sc_wrt_T n1 (S__T tau1)
  | degree_wrt_T_S__Forall : forall n1 sigma1,
    degree_Sc_wrt_T (S n1) sigma1 ->
    degree_Sc_wrt_T n1 (S__Forall sigma1).

Scheme degree_Sc_wrt_T_ind' := Induction for degree_Sc_wrt_T Sort Prop.

Combined Scheme degree_Sc_wrt_T_mutind from degree_Sc_wrt_T_ind'.

#[export] Hint Constructors degree_Sc_wrt_T : core lngen.

Inductive degree_Tm_wrt_T : nat -> Tm -> Prop :=
  | degree_wrt_T_t__Var_f : forall n1 tx1,
    degree_Tm_wrt_T n1 (t__Var_f tx1)
  | degree_wrt_T_t__Var_b : forall n1 n2,
    degree_Tm_wrt_T n1 (t__Var_b n2)
  | degree_wrt_T_t__Unit : forall n1,
    degree_Tm_wrt_T n1 (t__Unit)
  | degree_wrt_T_t__True : forall n1,
    degree_Tm_wrt_T n1 (t__True)
  | degree_wrt_T_t__False : forall n1,
    degree_Tm_wrt_T n1 (t__False)
  | degree_wrt_T_t__App : forall n1 t1 t2,
    degree_Tm_wrt_T n1 t1 ->
    degree_Tm_wrt_T n1 t2 ->
    degree_Tm_wrt_T n1 (t__App t1 t2)
  | degree_wrt_T_t__TApp : forall n1 t1 tau1,
    degree_Tm_wrt_T n1 t1 ->
    degree_T_wrt_T n1 tau1 ->
    degree_Tm_wrt_T n1 (t__TApp t1 tau1)
  | degree_wrt_T_t__Lam : forall n1 tau1 t1,
    degree_T_wrt_T n1 tau1 ->
    degree_Tm_wrt_T n1 t1 ->
    degree_Tm_wrt_T n1 (t__Lam tau1 t1)
  | degree_wrt_T_t__TLam : forall n1 t1,
    degree_Tm_wrt_T (S n1) t1 ->
    degree_Tm_wrt_T n1 (t__TLam t1).

Inductive degree_Tm_wrt_Tm : nat -> Tm -> Prop :=
  | degree_wrt_Tm_t__Var_f : forall n1 tx1,
    degree_Tm_wrt_Tm n1 (t__Var_f tx1)
  | degree_wrt_Tm_t__Var_b : forall n1 n2,
    lt n2 n1 ->
    degree_Tm_wrt_Tm n1 (t__Var_b n2)
  | degree_wrt_Tm_t__Unit : forall n1,
    degree_Tm_wrt_Tm n1 (t__Unit)
  | degree_wrt_Tm_t__True : forall n1,
    degree_Tm_wrt_Tm n1 (t__True)
  | degree_wrt_Tm_t__False : forall n1,
    degree_Tm_wrt_Tm n1 (t__False)
  | degree_wrt_Tm_t__App : forall n1 t1 t2,
    degree_Tm_wrt_Tm n1 t1 ->
    degree_Tm_wrt_Tm n1 t2 ->
    degree_Tm_wrt_Tm n1 (t__App t1 t2)
  | degree_wrt_Tm_t__TApp : forall n1 t1 tau1,
    degree_Tm_wrt_Tm n1 t1 ->
    degree_Tm_wrt_Tm n1 (t__TApp t1 tau1)
  | degree_wrt_Tm_t__Lam : forall n1 tau1 t1,
    degree_Tm_wrt_Tm (S n1) t1 ->
    degree_Tm_wrt_Tm n1 (t__Lam tau1 t1)
  | degree_wrt_Tm_t__TLam : forall n1 t1,
    degree_Tm_wrt_Tm n1 t1 ->
    degree_Tm_wrt_Tm n1 (t__TLam t1).

Scheme degree_Tm_wrt_T_ind' := Induction for degree_Tm_wrt_T Sort Prop.

Combined Scheme degree_Tm_wrt_T_mutind from degree_Tm_wrt_T_ind'.

Scheme degree_Tm_wrt_Tm_ind' := Induction for degree_Tm_wrt_Tm Sort Prop.

Combined Scheme degree_Tm_wrt_Tm_mutind from degree_Tm_wrt_Tm_ind'.

#[export] Hint Constructors degree_Tm_wrt_T : core lngen.

#[export] Hint Constructors degree_Tm_wrt_Tm : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_Ex : Ex -> Set :=
  | lc_set_e__Var_f : forall x1,
    lc_set_Ex (e__Var_f x1)
  | lc_set_e__Unit :
    lc_set_Ex (e__Unit)
  | lc_set_e__App : forall e1 e2,
    lc_set_Ex e1 ->
    lc_set_Ex e2 ->
    lc_set_Ex (e__App e1 e2)
  | lc_set_e__Lam : forall e1,
    (forall x1 : var, lc_set_Ex (open_Ex_wrt_Ex e1 (e__Var_f x1))) ->
    lc_set_Ex (e__Lam e1)
  | lc_set_e__Let : forall e1 e2,
    lc_set_Ex e1 ->
    (forall x1 : var, lc_set_Ex (open_Ex_wrt_Ex e2 (e__Var_f x1))) ->
    lc_set_Ex (e__Let e1 e2).

Scheme lc_Ex_ind' := Induction for lc_Ex Sort Prop.

Combined Scheme lc_Ex_mutind from lc_Ex_ind'.

Scheme lc_set_Ex_ind' := Induction for lc_set_Ex Sort Prop.

Combined Scheme lc_set_Ex_mutind from lc_set_Ex_ind'.

Scheme lc_set_Ex_rec' := Induction for lc_set_Ex Sort Set.

Combined Scheme lc_set_Ex_mutrec from lc_set_Ex_rec'.

#[export] Hint Constructors lc_Ex : core lngen.

#[export] Hint Constructors lc_set_Ex : core lngen.

Inductive lc_set_T : T -> Set :=
  | lc_set_T__Var_f : forall alpha1,
    lc_set_T (T__Var_f alpha1)
  | lc_set_T__Unit :
    lc_set_T (T__Unit)
  | lc_set_T__Bool :
    lc_set_T (T__Bool)
  | lc_set_T__Fun : forall tau1 tau2,
    lc_set_T tau1 ->
    lc_set_T tau2 ->
    lc_set_T (T__Fun tau1 tau2).

Scheme lc_T_ind' := Induction for lc_T Sort Prop.

Combined Scheme lc_T_mutind from lc_T_ind'.

Scheme lc_set_T_ind' := Induction for lc_set_T Sort Prop.

Combined Scheme lc_set_T_mutind from lc_set_T_ind'.

Scheme lc_set_T_rec' := Induction for lc_set_T Sort Set.

Combined Scheme lc_set_T_mutrec from lc_set_T_rec'.

#[export] Hint Constructors lc_T : core lngen.

#[export] Hint Constructors lc_set_T : core lngen.

Inductive lc_set_Sc : Sc -> Set :=
  | lc_set_S__T : forall tau1,
    lc_set_T tau1 ->
    lc_set_Sc (S__T tau1)
  | lc_set_S__Forall : forall sigma1,
    (forall alpha1 : skvar, lc_set_Sc (open_Sc_wrt_T sigma1 (T__Var_f alpha1))) ->
    lc_set_Sc (S__Forall sigma1).

Scheme lc_Sc_ind' := Induction for lc_Sc Sort Prop.

Combined Scheme lc_Sc_mutind from lc_Sc_ind'.

Scheme lc_set_Sc_ind' := Induction for lc_set_Sc Sort Prop.

Combined Scheme lc_set_Sc_mutind from lc_set_Sc_ind'.

Scheme lc_set_Sc_rec' := Induction for lc_set_Sc Sort Set.

Combined Scheme lc_set_Sc_mutrec from lc_set_Sc_rec'.

#[export] Hint Constructors lc_Sc : core lngen.

#[export] Hint Constructors lc_set_Sc : core lngen.

Inductive lc_set_Tm : Tm -> Set :=
  | lc_set_t__Var_f : forall tx1,
    lc_set_Tm (t__Var_f tx1)
  | lc_set_t__Unit :
    lc_set_Tm (t__Unit)
  | lc_set_t__True :
    lc_set_Tm (t__True)
  | lc_set_t__False :
    lc_set_Tm (t__False)
  | lc_set_t__App : forall t1 t2,
    lc_set_Tm t1 ->
    lc_set_Tm t2 ->
    lc_set_Tm (t__App t1 t2)
  | lc_set_t__TApp : forall t1 tau1,
    lc_set_Tm t1 ->
    lc_set_T tau1 ->
    lc_set_Tm (t__TApp t1 tau1)
  | lc_set_t__Lam : forall tau1 t1,
    lc_set_T tau1 ->
    (forall tx1 : tvar, lc_set_Tm (open_Tm_wrt_Tm t1 (t__Var_f tx1))) ->
    lc_set_Tm (t__Lam tau1 t1)
  | lc_set_t__TLam : forall t1,
    (forall alpha1 : skvar, lc_set_Tm (open_Tm_wrt_T t1 (T__Var_f alpha1))) ->
    lc_set_Tm (t__TLam t1).

Scheme lc_Tm_ind' := Induction for lc_Tm Sort Prop.

Combined Scheme lc_Tm_mutind from lc_Tm_ind'.

Scheme lc_set_Tm_ind' := Induction for lc_set_Tm Sort Prop.

Combined Scheme lc_set_Tm_mutind from lc_set_Tm_ind'.

Scheme lc_set_Tm_rec' := Induction for lc_set_Tm Sort Set.

Combined Scheme lc_set_Tm_mutrec from lc_set_Tm_rec'.

#[export] Hint Constructors lc_Tm : core lngen.

#[export] Hint Constructors lc_set_Tm : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_Ex_wrt_Ex e1 := forall x1, lc_Ex (open_Ex_wrt_Ex e1 (e__Var_f x1)).

#[export] Hint Unfold body_Ex_wrt_Ex : core.

Definition body_T_wrt_T T1 := forall beta1, lc_T (open_T_wrt_T T1 (T__Var_f beta1)).

#[export] Hint Unfold body_T_wrt_T : core.

Definition body_Sc_wrt_T Sc1 := forall beta1, lc_Sc (open_Sc_wrt_T Sc1 (T__Var_f beta1)).

#[export] Hint Unfold body_Sc_wrt_T : core.

Definition body_Tm_wrt_T t1 := forall beta1, lc_Tm (open_Tm_wrt_T t1 (T__Var_f beta1)).

Definition body_Tm_wrt_Tm t1 := forall tx1, lc_Tm (open_Tm_wrt_Tm t1 (t__Var_f tx1)).

#[export] Hint Unfold body_Tm_wrt_T : core.

#[export] Hint Unfold body_Tm_wrt_Tm : core.


(* *********************************************************************** *)
(** * Tactic support *)

(** Additional hint declarations. *)

(** Roger: changed out pluss_le_compat for Nat.add_le_mono because of *)
(** deprecation, see CoqLNOutputDefinitions.hs *)

(*#[export] Hint Resolve plus_le_compat : *)
#[export] Hint Resolve Nat.add_le_mono : lngen.

(** Redefine some tactics. *)

Ltac default_case_split ::=
  first
    [ progress destruct_notin
    | progress destruct_sum
    | progress safe_f_equal
    ].


(* *********************************************************************** *)
(** * Theorems about [size] *)

Ltac default_auto ::= auto with arith lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma size_Ex_min_mutual :
(forall e1, 1 <= size_Ex e1).
Proof.
apply_mutual_ind Ex_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_Ex_min :
forall e1, 1 <= size_Ex e1.
Proof.
pose proof size_Ex_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_Ex_min : lngen.

(* begin hide *)

Lemma size_T_min_mutual :
(forall T1, 1 <= size_T T1).
Proof.
apply_mutual_ind T_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_T_min :
forall T1, 1 <= size_T T1.
Proof.
pose proof size_T_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_T_min : lngen.

(* begin hide *)

Lemma size_Sc_min_mutual :
(forall Sc1, 1 <= size_Sc Sc1).
Proof.
apply_mutual_ind Sc_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_Sc_min :
forall Sc1, 1 <= size_Sc Sc1.
Proof.
pose proof size_Sc_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_Sc_min : lngen.

(* begin hide *)

Lemma size_Tm_min_mutual :
(forall t1, 1 <= size_Tm t1).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_Tm_min :
forall t1, 1 <= size_Tm t1.
Proof.
pose proof size_Tm_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_Tm_min : lngen.

(* begin hide *)

Lemma size_Ex_close_Ex_wrt_Ex_rec_mutual :
(forall e1 x1 n1,
  size_Ex (close_Ex_wrt_Ex_rec n1 x1 e1) = size_Ex e1).
Proof.
apply_mutual_ind Ex_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_Ex_close_Ex_wrt_Ex_rec :
forall e1 x1 n1,
  size_Ex (close_Ex_wrt_Ex_rec n1 x1 e1) = size_Ex e1.
Proof.
pose proof size_Ex_close_Ex_wrt_Ex_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_Ex_close_Ex_wrt_Ex_rec : lngen.
#[export] Hint Rewrite size_Ex_close_Ex_wrt_Ex_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_T_close_T_wrt_T_rec_mutual :
(forall T1 beta1 n1,
  size_T (close_T_wrt_T_rec n1 beta1 T1) = size_T T1).
Proof.
apply_mutual_ind T_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_T_close_T_wrt_T_rec :
forall T1 beta1 n1,
  size_T (close_T_wrt_T_rec n1 beta1 T1) = size_T T1.
Proof.
pose proof size_T_close_T_wrt_T_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_T_close_T_wrt_T_rec : lngen.
#[export] Hint Rewrite size_T_close_T_wrt_T_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_Sc_close_Sc_wrt_T_rec_mutual :
(forall Sc1 beta1 n1,
  size_Sc (close_Sc_wrt_T_rec n1 beta1 Sc1) = size_Sc Sc1).
Proof.
apply_mutual_ind Sc_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_Sc_close_Sc_wrt_T_rec :
forall Sc1 beta1 n1,
  size_Sc (close_Sc_wrt_T_rec n1 beta1 Sc1) = size_Sc Sc1.
Proof.
pose proof size_Sc_close_Sc_wrt_T_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_Sc_close_Sc_wrt_T_rec : lngen.
#[export] Hint Rewrite size_Sc_close_Sc_wrt_T_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_Tm_close_Tm_wrt_T_rec_mutual :
(forall t1 beta1 n1,
  size_Tm (close_Tm_wrt_T_rec n1 beta1 t1) = size_Tm t1).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_Tm_close_Tm_wrt_T_rec :
forall t1 beta1 n1,
  size_Tm (close_Tm_wrt_T_rec n1 beta1 t1) = size_Tm t1.
Proof.
pose proof size_Tm_close_Tm_wrt_T_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_Tm_close_Tm_wrt_T_rec : lngen.
#[export] Hint Rewrite size_Tm_close_Tm_wrt_T_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_Tm_close_Tm_wrt_Tm_rec_mutual :
(forall t1 tx1 n1,
  size_Tm (close_Tm_wrt_Tm_rec n1 tx1 t1) = size_Tm t1).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_Tm_close_Tm_wrt_Tm_rec :
forall t1 tx1 n1,
  size_Tm (close_Tm_wrt_Tm_rec n1 tx1 t1) = size_Tm t1.
Proof.
pose proof size_Tm_close_Tm_wrt_Tm_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_Tm_close_Tm_wrt_Tm_rec : lngen.
#[export] Hint Rewrite size_Tm_close_Tm_wrt_Tm_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_Ex_close_Ex_wrt_Ex :
forall e1 x1,
  size_Ex (close_Ex_wrt_Ex x1 e1) = size_Ex e1.
Proof.
unfold close_Ex_wrt_Ex; default_simp.
Qed.

#[export] Hint Resolve size_Ex_close_Ex_wrt_Ex : lngen.
#[export] Hint Rewrite size_Ex_close_Ex_wrt_Ex using solve [auto] : lngen.

Lemma size_T_close_T_wrt_T :
forall T1 beta1,
  size_T (close_T_wrt_T beta1 T1) = size_T T1.
Proof.
unfold close_T_wrt_T; default_simp.
Qed.

#[export] Hint Resolve size_T_close_T_wrt_T : lngen.
#[export] Hint Rewrite size_T_close_T_wrt_T using solve [auto] : lngen.

Lemma size_Sc_close_Sc_wrt_T :
forall Sc1 beta1,
  size_Sc (close_Sc_wrt_T beta1 Sc1) = size_Sc Sc1.
Proof.
unfold close_Sc_wrt_T; default_simp.
Qed.

#[export] Hint Resolve size_Sc_close_Sc_wrt_T : lngen.
#[export] Hint Rewrite size_Sc_close_Sc_wrt_T using solve [auto] : lngen.

Lemma size_Tm_close_Tm_wrt_T :
forall t1 beta1,
  size_Tm (close_Tm_wrt_T beta1 t1) = size_Tm t1.
Proof.
unfold close_Tm_wrt_T; default_simp.
Qed.

#[export] Hint Resolve size_Tm_close_Tm_wrt_T : lngen.
#[export] Hint Rewrite size_Tm_close_Tm_wrt_T using solve [auto] : lngen.

Lemma size_Tm_close_Tm_wrt_Tm :
forall t1 tx1,
  size_Tm (close_Tm_wrt_Tm tx1 t1) = size_Tm t1.
Proof.
unfold close_Tm_wrt_Tm; default_simp.
Qed.

#[export] Hint Resolve size_Tm_close_Tm_wrt_Tm : lngen.
#[export] Hint Rewrite size_Tm_close_Tm_wrt_Tm using solve [auto] : lngen.

(* begin hide *)

Lemma size_Ex_open_Ex_wrt_Ex_rec_mutual :
(forall e1 e2 n1,
  size_Ex e1 <= size_Ex (open_Ex_wrt_Ex_rec n1 e2 e1)).
Proof.
apply_mutual_ind Ex_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_Ex_open_Ex_wrt_Ex_rec :
forall e1 e2 n1,
  size_Ex e1 <= size_Ex (open_Ex_wrt_Ex_rec n1 e2 e1).
Proof.
pose proof size_Ex_open_Ex_wrt_Ex_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_Ex_open_Ex_wrt_Ex_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_T_open_T_wrt_T_rec_mutual :
(forall T1 T2 n1,
  size_T T1 <= size_T (open_T_wrt_T_rec n1 T2 T1)).
Proof.
apply_mutual_ind T_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_T_open_T_wrt_T_rec :
forall T1 T2 n1,
  size_T T1 <= size_T (open_T_wrt_T_rec n1 T2 T1).
Proof.
pose proof size_T_open_T_wrt_T_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_T_open_T_wrt_T_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_Sc_open_Sc_wrt_T_rec_mutual :
(forall Sc1 T1 n1,
  size_Sc Sc1 <= size_Sc (open_Sc_wrt_T_rec n1 T1 Sc1)).
Proof.
apply_mutual_ind Sc_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_Sc_open_Sc_wrt_T_rec :
forall Sc1 T1 n1,
  size_Sc Sc1 <= size_Sc (open_Sc_wrt_T_rec n1 T1 Sc1).
Proof.
pose proof size_Sc_open_Sc_wrt_T_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_Sc_open_Sc_wrt_T_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_Tm_open_Tm_wrt_T_rec_mutual :
(forall t1 T1 n1,
  size_Tm t1 <= size_Tm (open_Tm_wrt_T_rec n1 T1 t1)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_Tm_open_Tm_wrt_T_rec :
forall t1 T1 n1,
  size_Tm t1 <= size_Tm (open_Tm_wrt_T_rec n1 T1 t1).
Proof.
pose proof size_Tm_open_Tm_wrt_T_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_Tm_open_Tm_wrt_T_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_Tm_open_Tm_wrt_Tm_rec_mutual :
(forall t1 t2 n1,
  size_Tm t1 <= size_Tm (open_Tm_wrt_Tm_rec n1 t2 t1)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_Tm_open_Tm_wrt_Tm_rec :
forall t1 t2 n1,
  size_Tm t1 <= size_Tm (open_Tm_wrt_Tm_rec n1 t2 t1).
Proof.
pose proof size_Tm_open_Tm_wrt_Tm_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_Tm_open_Tm_wrt_Tm_rec : lngen.

(* end hide *)

Lemma size_Ex_open_Ex_wrt_Ex :
forall e1 e2,
  size_Ex e1 <= size_Ex (open_Ex_wrt_Ex e1 e2).
Proof.
unfold open_Ex_wrt_Ex; default_simp.
Qed.

#[export] Hint Resolve size_Ex_open_Ex_wrt_Ex : lngen.

Lemma size_T_open_T_wrt_T :
forall T1 T2,
  size_T T1 <= size_T (open_T_wrt_T T1 T2).
Proof.
unfold open_T_wrt_T; default_simp.
Qed.

#[export] Hint Resolve size_T_open_T_wrt_T : lngen.

Lemma size_Sc_open_Sc_wrt_T :
forall Sc1 T1,
  size_Sc Sc1 <= size_Sc (open_Sc_wrt_T Sc1 T1).
Proof.
unfold open_Sc_wrt_T; default_simp.
Qed.

#[export] Hint Resolve size_Sc_open_Sc_wrt_T : lngen.

Lemma size_Tm_open_Tm_wrt_T :
forall t1 T1,
  size_Tm t1 <= size_Tm (open_Tm_wrt_T t1 T1).
Proof.
unfold open_Tm_wrt_T; default_simp.
Qed.

#[export] Hint Resolve size_Tm_open_Tm_wrt_T : lngen.

Lemma size_Tm_open_Tm_wrt_Tm :
forall t1 t2,
  size_Tm t1 <= size_Tm (open_Tm_wrt_Tm t1 t2).
Proof.
unfold open_Tm_wrt_Tm; default_simp.
Qed.

#[export] Hint Resolve size_Tm_open_Tm_wrt_Tm : lngen.

(* begin hide *)

Lemma size_Ex_open_Ex_wrt_Ex_rec_var_mutual :
(forall e1 x1 n1,
  size_Ex (open_Ex_wrt_Ex_rec n1 (e__Var_f x1) e1) = size_Ex e1).
Proof.
apply_mutual_ind Ex_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_Ex_open_Ex_wrt_Ex_rec_var :
forall e1 x1 n1,
  size_Ex (open_Ex_wrt_Ex_rec n1 (e__Var_f x1) e1) = size_Ex e1.
Proof.
pose proof size_Ex_open_Ex_wrt_Ex_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_Ex_open_Ex_wrt_Ex_rec_var : lngen.
#[export] Hint Rewrite size_Ex_open_Ex_wrt_Ex_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_T_open_T_wrt_T_rec_var_mutual :
(forall T1 beta1 n1,
  size_T (open_T_wrt_T_rec n1 (T__Var_f beta1) T1) = size_T T1).
Proof.
apply_mutual_ind T_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_T_open_T_wrt_T_rec_var :
forall T1 beta1 n1,
  size_T (open_T_wrt_T_rec n1 (T__Var_f beta1) T1) = size_T T1.
Proof.
pose proof size_T_open_T_wrt_T_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_T_open_T_wrt_T_rec_var : lngen.
#[export] Hint Rewrite size_T_open_T_wrt_T_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_Sc_open_Sc_wrt_T_rec_var_mutual :
(forall Sc1 beta1 n1,
  size_Sc (open_Sc_wrt_T_rec n1 (T__Var_f beta1) Sc1) = size_Sc Sc1).
Proof.
apply_mutual_ind Sc_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_Sc_open_Sc_wrt_T_rec_var :
forall Sc1 beta1 n1,
  size_Sc (open_Sc_wrt_T_rec n1 (T__Var_f beta1) Sc1) = size_Sc Sc1.
Proof.
pose proof size_Sc_open_Sc_wrt_T_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_Sc_open_Sc_wrt_T_rec_var : lngen.
#[export] Hint Rewrite size_Sc_open_Sc_wrt_T_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_Tm_open_Tm_wrt_T_rec_var_mutual :
(forall t1 beta1 n1,
  size_Tm (open_Tm_wrt_T_rec n1 (T__Var_f beta1) t1) = size_Tm t1).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_Tm_open_Tm_wrt_T_rec_var :
forall t1 beta1 n1,
  size_Tm (open_Tm_wrt_T_rec n1 (T__Var_f beta1) t1) = size_Tm t1.
Proof.
pose proof size_Tm_open_Tm_wrt_T_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_Tm_open_Tm_wrt_T_rec_var : lngen.
#[export] Hint Rewrite size_Tm_open_Tm_wrt_T_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_Tm_open_Tm_wrt_Tm_rec_var_mutual :
(forall t1 tx1 n1,
  size_Tm (open_Tm_wrt_Tm_rec n1 (t__Var_f tx1) t1) = size_Tm t1).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_Tm_open_Tm_wrt_Tm_rec_var :
forall t1 tx1 n1,
  size_Tm (open_Tm_wrt_Tm_rec n1 (t__Var_f tx1) t1) = size_Tm t1.
Proof.
pose proof size_Tm_open_Tm_wrt_Tm_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_Tm_open_Tm_wrt_Tm_rec_var : lngen.
#[export] Hint Rewrite size_Tm_open_Tm_wrt_Tm_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_Ex_open_Ex_wrt_Ex_var :
forall e1 x1,
  size_Ex (open_Ex_wrt_Ex e1 (e__Var_f x1)) = size_Ex e1.
Proof.
unfold open_Ex_wrt_Ex; default_simp.
Qed.

#[export] Hint Resolve size_Ex_open_Ex_wrt_Ex_var : lngen.
#[export] Hint Rewrite size_Ex_open_Ex_wrt_Ex_var using solve [auto] : lngen.

Lemma size_T_open_T_wrt_T_var :
forall T1 beta1,
  size_T (open_T_wrt_T T1 (T__Var_f beta1)) = size_T T1.
Proof.
unfold open_T_wrt_T; default_simp.
Qed.

#[export] Hint Resolve size_T_open_T_wrt_T_var : lngen.
#[export] Hint Rewrite size_T_open_T_wrt_T_var using solve [auto] : lngen.

Lemma size_Sc_open_Sc_wrt_T_var :
forall Sc1 beta1,
  size_Sc (open_Sc_wrt_T Sc1 (T__Var_f beta1)) = size_Sc Sc1.
Proof.
unfold open_Sc_wrt_T; default_simp.
Qed.

#[export] Hint Resolve size_Sc_open_Sc_wrt_T_var : lngen.
#[export] Hint Rewrite size_Sc_open_Sc_wrt_T_var using solve [auto] : lngen.

Lemma size_Tm_open_Tm_wrt_T_var :
forall t1 beta1,
  size_Tm (open_Tm_wrt_T t1 (T__Var_f beta1)) = size_Tm t1.
Proof.
unfold open_Tm_wrt_T; default_simp.
Qed.

#[export] Hint Resolve size_Tm_open_Tm_wrt_T_var : lngen.
#[export] Hint Rewrite size_Tm_open_Tm_wrt_T_var using solve [auto] : lngen.

Lemma size_Tm_open_Tm_wrt_Tm_var :
forall t1 tx1,
  size_Tm (open_Tm_wrt_Tm t1 (t__Var_f tx1)) = size_Tm t1.
Proof.
unfold open_Tm_wrt_Tm; default_simp.
Qed.

#[export] Hint Resolve size_Tm_open_Tm_wrt_Tm_var : lngen.
#[export] Hint Rewrite size_Tm_open_Tm_wrt_Tm_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_Ex_wrt_Ex_S_mutual :
(forall n1 e1,
  degree_Ex_wrt_Ex n1 e1 ->
  degree_Ex_wrt_Ex (S n1) e1).
Proof.
apply_mutual_ind degree_Ex_wrt_Ex_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_Ex_wrt_Ex_S :
forall n1 e1,
  degree_Ex_wrt_Ex n1 e1 ->
  degree_Ex_wrt_Ex (S n1) e1.
Proof.
pose proof degree_Ex_wrt_Ex_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_Ex_wrt_Ex_S : lngen.

(* begin hide *)

Lemma degree_T_wrt_T_S_mutual :
(forall n1 T1,
  degree_T_wrt_T n1 T1 ->
  degree_T_wrt_T (S n1) T1).
Proof.
apply_mutual_ind degree_T_wrt_T_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_T_wrt_T_S :
forall n1 T1,
  degree_T_wrt_T n1 T1 ->
  degree_T_wrt_T (S n1) T1.
Proof.
pose proof degree_T_wrt_T_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_T_wrt_T_S : lngen.

(* begin hide *)

Lemma degree_Sc_wrt_T_S_mutual :
(forall n1 Sc1,
  degree_Sc_wrt_T n1 Sc1 ->
  degree_Sc_wrt_T (S n1) Sc1).
Proof.
apply_mutual_ind degree_Sc_wrt_T_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_Sc_wrt_T_S :
forall n1 Sc1,
  degree_Sc_wrt_T n1 Sc1 ->
  degree_Sc_wrt_T (S n1) Sc1.
Proof.
pose proof degree_Sc_wrt_T_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_Sc_wrt_T_S : lngen.

(* begin hide *)

Lemma degree_Tm_wrt_T_S_mutual :
(forall n1 t1,
  degree_Tm_wrt_T n1 t1 ->
  degree_Tm_wrt_T (S n1) t1).
Proof.
apply_mutual_ind degree_Tm_wrt_T_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_Tm_wrt_T_S :
forall n1 t1,
  degree_Tm_wrt_T n1 t1 ->
  degree_Tm_wrt_T (S n1) t1.
Proof.
pose proof degree_Tm_wrt_T_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_Tm_wrt_T_S : lngen.

(* begin hide *)

Lemma degree_Tm_wrt_Tm_S_mutual :
(forall n1 t1,
  degree_Tm_wrt_Tm n1 t1 ->
  degree_Tm_wrt_Tm (S n1) t1).
Proof.
apply_mutual_ind degree_Tm_wrt_Tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_Tm_wrt_Tm_S :
forall n1 t1,
  degree_Tm_wrt_Tm n1 t1 ->
  degree_Tm_wrt_Tm (S n1) t1.
Proof.
pose proof degree_Tm_wrt_Tm_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_Tm_wrt_Tm_S : lngen.

Lemma degree_Ex_wrt_Ex_O :
forall n1 e1,
  degree_Ex_wrt_Ex O e1 ->
  degree_Ex_wrt_Ex n1 e1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_Ex_wrt_Ex_O : lngen.

Lemma degree_T_wrt_T_O :
forall n1 T1,
  degree_T_wrt_T O T1 ->
  degree_T_wrt_T n1 T1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_T_wrt_T_O : lngen.

Lemma degree_Sc_wrt_T_O :
forall n1 Sc1,
  degree_Sc_wrt_T O Sc1 ->
  degree_Sc_wrt_T n1 Sc1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_Sc_wrt_T_O : lngen.

Lemma degree_Tm_wrt_T_O :
forall n1 t1,
  degree_Tm_wrt_T O t1 ->
  degree_Tm_wrt_T n1 t1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_Tm_wrt_T_O : lngen.

Lemma degree_Tm_wrt_Tm_O :
forall n1 t1,
  degree_Tm_wrt_Tm O t1 ->
  degree_Tm_wrt_Tm n1 t1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_Tm_wrt_Tm_O : lngen.

(* begin hide *)

Lemma degree_Ex_wrt_Ex_close_Ex_wrt_Ex_rec_mutual :
(forall e1 x1 n1,
  degree_Ex_wrt_Ex n1 e1 ->
  degree_Ex_wrt_Ex (S n1) (close_Ex_wrt_Ex_rec n1 x1 e1)).
Proof.
apply_mutual_ind Ex_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_Ex_wrt_Ex_close_Ex_wrt_Ex_rec :
forall e1 x1 n1,
  degree_Ex_wrt_Ex n1 e1 ->
  degree_Ex_wrt_Ex (S n1) (close_Ex_wrt_Ex_rec n1 x1 e1).
Proof.
pose proof degree_Ex_wrt_Ex_close_Ex_wrt_Ex_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_Ex_wrt_Ex_close_Ex_wrt_Ex_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_T_wrt_T_close_T_wrt_T_rec_mutual :
(forall T1 beta1 n1,
  degree_T_wrt_T n1 T1 ->
  degree_T_wrt_T (S n1) (close_T_wrt_T_rec n1 beta1 T1)).
Proof.
apply_mutual_ind T_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_T_wrt_T_close_T_wrt_T_rec :
forall T1 beta1 n1,
  degree_T_wrt_T n1 T1 ->
  degree_T_wrt_T (S n1) (close_T_wrt_T_rec n1 beta1 T1).
Proof.
pose proof degree_T_wrt_T_close_T_wrt_T_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_T_wrt_T_close_T_wrt_T_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Sc_wrt_T_close_Sc_wrt_T_rec_mutual :
(forall Sc1 beta1 n1,
  degree_Sc_wrt_T n1 Sc1 ->
  degree_Sc_wrt_T (S n1) (close_Sc_wrt_T_rec n1 beta1 Sc1)).
Proof.
apply_mutual_ind Sc_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_Sc_wrt_T_close_Sc_wrt_T_rec :
forall Sc1 beta1 n1,
  degree_Sc_wrt_T n1 Sc1 ->
  degree_Sc_wrt_T (S n1) (close_Sc_wrt_T_rec n1 beta1 Sc1).
Proof.
pose proof degree_Sc_wrt_T_close_Sc_wrt_T_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_Sc_wrt_T_close_Sc_wrt_T_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Tm_wrt_T_close_Tm_wrt_T_rec_mutual :
(forall t1 beta1 n1,
  degree_Tm_wrt_T n1 t1 ->
  degree_Tm_wrt_T (S n1) (close_Tm_wrt_T_rec n1 beta1 t1)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_Tm_wrt_T_close_Tm_wrt_T_rec :
forall t1 beta1 n1,
  degree_Tm_wrt_T n1 t1 ->
  degree_Tm_wrt_T (S n1) (close_Tm_wrt_T_rec n1 beta1 t1).
Proof.
pose proof degree_Tm_wrt_T_close_Tm_wrt_T_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_Tm_wrt_T_close_Tm_wrt_T_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Tm_wrt_T_close_Tm_wrt_Tm_rec_mutual :
(forall t1 tx1 n1 n2,
  degree_Tm_wrt_T n2 t1 ->
  degree_Tm_wrt_T n2 (close_Tm_wrt_Tm_rec n1 tx1 t1)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_Tm_wrt_T_close_Tm_wrt_Tm_rec :
forall t1 tx1 n1 n2,
  degree_Tm_wrt_T n2 t1 ->
  degree_Tm_wrt_T n2 (close_Tm_wrt_Tm_rec n1 tx1 t1).
Proof.
pose proof degree_Tm_wrt_T_close_Tm_wrt_Tm_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_Tm_wrt_T_close_Tm_wrt_Tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Tm_wrt_Tm_close_Tm_wrt_T_rec_mutual :
(forall t1 beta1 n1 n2,
  degree_Tm_wrt_Tm n2 t1 ->
  degree_Tm_wrt_Tm n2 (close_Tm_wrt_T_rec n1 beta1 t1)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_Tm_wrt_Tm_close_Tm_wrt_T_rec :
forall t1 beta1 n1 n2,
  degree_Tm_wrt_Tm n2 t1 ->
  degree_Tm_wrt_Tm n2 (close_Tm_wrt_T_rec n1 beta1 t1).
Proof.
pose proof degree_Tm_wrt_Tm_close_Tm_wrt_T_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_Tm_wrt_Tm_close_Tm_wrt_T_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Tm_wrt_Tm_close_Tm_wrt_Tm_rec_mutual :
(forall t1 tx1 n1,
  degree_Tm_wrt_Tm n1 t1 ->
  degree_Tm_wrt_Tm (S n1) (close_Tm_wrt_Tm_rec n1 tx1 t1)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_Tm_wrt_Tm_close_Tm_wrt_Tm_rec :
forall t1 tx1 n1,
  degree_Tm_wrt_Tm n1 t1 ->
  degree_Tm_wrt_Tm (S n1) (close_Tm_wrt_Tm_rec n1 tx1 t1).
Proof.
pose proof degree_Tm_wrt_Tm_close_Tm_wrt_Tm_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_Tm_wrt_Tm_close_Tm_wrt_Tm_rec : lngen.

(* end hide *)

Lemma degree_Ex_wrt_Ex_close_Ex_wrt_Ex :
forall e1 x1,
  degree_Ex_wrt_Ex 0 e1 ->
  degree_Ex_wrt_Ex 1 (close_Ex_wrt_Ex x1 e1).
Proof.
unfold close_Ex_wrt_Ex; default_simp.
Qed.

#[export] Hint Resolve degree_Ex_wrt_Ex_close_Ex_wrt_Ex : lngen.

Lemma degree_T_wrt_T_close_T_wrt_T :
forall T1 beta1,
  degree_T_wrt_T 0 T1 ->
  degree_T_wrt_T 1 (close_T_wrt_T beta1 T1).
Proof.
unfold close_T_wrt_T; default_simp.
Qed.

#[export] Hint Resolve degree_T_wrt_T_close_T_wrt_T : lngen.

Lemma degree_Sc_wrt_T_close_Sc_wrt_T :
forall Sc1 beta1,
  degree_Sc_wrt_T 0 Sc1 ->
  degree_Sc_wrt_T 1 (close_Sc_wrt_T beta1 Sc1).
Proof.
unfold close_Sc_wrt_T; default_simp.
Qed.

#[export] Hint Resolve degree_Sc_wrt_T_close_Sc_wrt_T : lngen.

Lemma degree_Tm_wrt_T_close_Tm_wrt_T :
forall t1 beta1,
  degree_Tm_wrt_T 0 t1 ->
  degree_Tm_wrt_T 1 (close_Tm_wrt_T beta1 t1).
Proof.
unfold close_Tm_wrt_T; default_simp.
Qed.

#[export] Hint Resolve degree_Tm_wrt_T_close_Tm_wrt_T : lngen.

Lemma degree_Tm_wrt_T_close_Tm_wrt_Tm :
forall t1 tx1 n1,
  degree_Tm_wrt_T n1 t1 ->
  degree_Tm_wrt_T n1 (close_Tm_wrt_Tm tx1 t1).
Proof.
unfold close_Tm_wrt_Tm; default_simp.
Qed.

#[export] Hint Resolve degree_Tm_wrt_T_close_Tm_wrt_Tm : lngen.

Lemma degree_Tm_wrt_Tm_close_Tm_wrt_T :
forall t1 beta1 n1,
  degree_Tm_wrt_Tm n1 t1 ->
  degree_Tm_wrt_Tm n1 (close_Tm_wrt_T beta1 t1).
Proof.
unfold close_Tm_wrt_T; default_simp.
Qed.

#[export] Hint Resolve degree_Tm_wrt_Tm_close_Tm_wrt_T : lngen.

Lemma degree_Tm_wrt_Tm_close_Tm_wrt_Tm :
forall t1 tx1,
  degree_Tm_wrt_Tm 0 t1 ->
  degree_Tm_wrt_Tm 1 (close_Tm_wrt_Tm tx1 t1).
Proof.
unfold close_Tm_wrt_Tm; default_simp.
Qed.

#[export] Hint Resolve degree_Tm_wrt_Tm_close_Tm_wrt_Tm : lngen.

(* begin hide *)

Lemma degree_Ex_wrt_Ex_close_Ex_wrt_Ex_rec_inv_mutual :
(forall e1 x1 n1,
  degree_Ex_wrt_Ex (S n1) (close_Ex_wrt_Ex_rec n1 x1 e1) ->
  degree_Ex_wrt_Ex n1 e1).
Proof.
apply_mutual_ind Ex_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_Ex_wrt_Ex_close_Ex_wrt_Ex_rec_inv :
forall e1 x1 n1,
  degree_Ex_wrt_Ex (S n1) (close_Ex_wrt_Ex_rec n1 x1 e1) ->
  degree_Ex_wrt_Ex n1 e1.
Proof.
pose proof degree_Ex_wrt_Ex_close_Ex_wrt_Ex_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_Ex_wrt_Ex_close_Ex_wrt_Ex_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_T_wrt_T_close_T_wrt_T_rec_inv_mutual :
(forall T1 beta1 n1,
  degree_T_wrt_T (S n1) (close_T_wrt_T_rec n1 beta1 T1) ->
  degree_T_wrt_T n1 T1).
Proof.
apply_mutual_ind T_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_T_wrt_T_close_T_wrt_T_rec_inv :
forall T1 beta1 n1,
  degree_T_wrt_T (S n1) (close_T_wrt_T_rec n1 beta1 T1) ->
  degree_T_wrt_T n1 T1.
Proof.
pose proof degree_T_wrt_T_close_T_wrt_T_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_T_wrt_T_close_T_wrt_T_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Sc_wrt_T_close_Sc_wrt_T_rec_inv_mutual :
(forall Sc1 beta1 n1,
  degree_Sc_wrt_T (S n1) (close_Sc_wrt_T_rec n1 beta1 Sc1) ->
  degree_Sc_wrt_T n1 Sc1).
Proof.
apply_mutual_ind Sc_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_Sc_wrt_T_close_Sc_wrt_T_rec_inv :
forall Sc1 beta1 n1,
  degree_Sc_wrt_T (S n1) (close_Sc_wrt_T_rec n1 beta1 Sc1) ->
  degree_Sc_wrt_T n1 Sc1.
Proof.
pose proof degree_Sc_wrt_T_close_Sc_wrt_T_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_Sc_wrt_T_close_Sc_wrt_T_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Tm_wrt_T_close_Tm_wrt_T_rec_inv_mutual :
(forall t1 beta1 n1,
  degree_Tm_wrt_T (S n1) (close_Tm_wrt_T_rec n1 beta1 t1) ->
  degree_Tm_wrt_T n1 t1).
Proof.
apply_mutual_ind Tm_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_Tm_wrt_T_close_Tm_wrt_T_rec_inv :
forall t1 beta1 n1,
  degree_Tm_wrt_T (S n1) (close_Tm_wrt_T_rec n1 beta1 t1) ->
  degree_Tm_wrt_T n1 t1.
Proof.
pose proof degree_Tm_wrt_T_close_Tm_wrt_T_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_Tm_wrt_T_close_Tm_wrt_T_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Tm_wrt_T_close_Tm_wrt_Tm_rec_inv_mutual :
(forall t1 tx1 n1 n2,
  degree_Tm_wrt_T n2 (close_Tm_wrt_Tm_rec n1 tx1 t1) ->
  degree_Tm_wrt_T n2 t1).
Proof.
apply_mutual_ind Tm_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_Tm_wrt_T_close_Tm_wrt_Tm_rec_inv :
forall t1 tx1 n1 n2,
  degree_Tm_wrt_T n2 (close_Tm_wrt_Tm_rec n1 tx1 t1) ->
  degree_Tm_wrt_T n2 t1.
Proof.
pose proof degree_Tm_wrt_T_close_Tm_wrt_Tm_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_Tm_wrt_T_close_Tm_wrt_Tm_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Tm_wrt_Tm_close_Tm_wrt_T_rec_inv_mutual :
(forall t1 beta1 n1 n2,
  degree_Tm_wrt_Tm n2 (close_Tm_wrt_T_rec n1 beta1 t1) ->
  degree_Tm_wrt_Tm n2 t1).
Proof.
apply_mutual_ind Tm_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_Tm_wrt_Tm_close_Tm_wrt_T_rec_inv :
forall t1 beta1 n1 n2,
  degree_Tm_wrt_Tm n2 (close_Tm_wrt_T_rec n1 beta1 t1) ->
  degree_Tm_wrt_Tm n2 t1.
Proof.
pose proof degree_Tm_wrt_Tm_close_Tm_wrt_T_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_Tm_wrt_Tm_close_Tm_wrt_T_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Tm_wrt_Tm_close_Tm_wrt_Tm_rec_inv_mutual :
(forall t1 tx1 n1,
  degree_Tm_wrt_Tm (S n1) (close_Tm_wrt_Tm_rec n1 tx1 t1) ->
  degree_Tm_wrt_Tm n1 t1).
Proof.
apply_mutual_ind Tm_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_Tm_wrt_Tm_close_Tm_wrt_Tm_rec_inv :
forall t1 tx1 n1,
  degree_Tm_wrt_Tm (S n1) (close_Tm_wrt_Tm_rec n1 tx1 t1) ->
  degree_Tm_wrt_Tm n1 t1.
Proof.
pose proof degree_Tm_wrt_Tm_close_Tm_wrt_Tm_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_Tm_wrt_Tm_close_Tm_wrt_Tm_rec_inv : lngen.

(* end hide *)

Lemma degree_Ex_wrt_Ex_close_Ex_wrt_Ex_inv :
forall e1 x1,
  degree_Ex_wrt_Ex 1 (close_Ex_wrt_Ex x1 e1) ->
  degree_Ex_wrt_Ex 0 e1.
Proof.
unfold close_Ex_wrt_Ex; eauto with lngen.
Qed.

#[export] Hint Immediate degree_Ex_wrt_Ex_close_Ex_wrt_Ex_inv : lngen.

Lemma degree_T_wrt_T_close_T_wrt_T_inv :
forall T1 beta1,
  degree_T_wrt_T 1 (close_T_wrt_T beta1 T1) ->
  degree_T_wrt_T 0 T1.
Proof.
unfold close_T_wrt_T; eauto with lngen.
Qed.

#[export] Hint Immediate degree_T_wrt_T_close_T_wrt_T_inv : lngen.

Lemma degree_Sc_wrt_T_close_Sc_wrt_T_inv :
forall Sc1 beta1,
  degree_Sc_wrt_T 1 (close_Sc_wrt_T beta1 Sc1) ->
  degree_Sc_wrt_T 0 Sc1.
Proof.
unfold close_Sc_wrt_T; eauto with lngen.
Qed.

#[export] Hint Immediate degree_Sc_wrt_T_close_Sc_wrt_T_inv : lngen.

Lemma degree_Tm_wrt_T_close_Tm_wrt_T_inv :
forall t1 beta1,
  degree_Tm_wrt_T 1 (close_Tm_wrt_T beta1 t1) ->
  degree_Tm_wrt_T 0 t1.
Proof.
unfold close_Tm_wrt_T; eauto with lngen.
Qed.

#[export] Hint Immediate degree_Tm_wrt_T_close_Tm_wrt_T_inv : lngen.

Lemma degree_Tm_wrt_T_close_Tm_wrt_Tm_inv :
forall t1 tx1 n1,
  degree_Tm_wrt_T n1 (close_Tm_wrt_Tm tx1 t1) ->
  degree_Tm_wrt_T n1 t1.
Proof.
unfold close_Tm_wrt_Tm; eauto with lngen.
Qed.

#[export] Hint Immediate degree_Tm_wrt_T_close_Tm_wrt_Tm_inv : lngen.

Lemma degree_Tm_wrt_Tm_close_Tm_wrt_T_inv :
forall t1 beta1 n1,
  degree_Tm_wrt_Tm n1 (close_Tm_wrt_T beta1 t1) ->
  degree_Tm_wrt_Tm n1 t1.
Proof.
unfold close_Tm_wrt_T; eauto with lngen.
Qed.

#[export] Hint Immediate degree_Tm_wrt_Tm_close_Tm_wrt_T_inv : lngen.

Lemma degree_Tm_wrt_Tm_close_Tm_wrt_Tm_inv :
forall t1 tx1,
  degree_Tm_wrt_Tm 1 (close_Tm_wrt_Tm tx1 t1) ->
  degree_Tm_wrt_Tm 0 t1.
Proof.
unfold close_Tm_wrt_Tm; eauto with lngen.
Qed.

#[export] Hint Immediate degree_Tm_wrt_Tm_close_Tm_wrt_Tm_inv : lngen.

(* begin hide *)

Lemma degree_Ex_wrt_Ex_open_Ex_wrt_Ex_rec_mutual :
(forall e1 e2 n1,
  degree_Ex_wrt_Ex (S n1) e1 ->
  degree_Ex_wrt_Ex n1 e2 ->
  degree_Ex_wrt_Ex n1 (open_Ex_wrt_Ex_rec n1 e2 e1)).
Proof.
apply_mutual_ind Ex_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_Ex_wrt_Ex_open_Ex_wrt_Ex_rec :
forall e1 e2 n1,
  degree_Ex_wrt_Ex (S n1) e1 ->
  degree_Ex_wrt_Ex n1 e2 ->
  degree_Ex_wrt_Ex n1 (open_Ex_wrt_Ex_rec n1 e2 e1).
Proof.
pose proof degree_Ex_wrt_Ex_open_Ex_wrt_Ex_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_Ex_wrt_Ex_open_Ex_wrt_Ex_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_T_wrt_T_open_T_wrt_T_rec_mutual :
(forall T1 T2 n1,
  degree_T_wrt_T (S n1) T1 ->
  degree_T_wrt_T n1 T2 ->
  degree_T_wrt_T n1 (open_T_wrt_T_rec n1 T2 T1)).
Proof.
apply_mutual_ind T_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_T_wrt_T_open_T_wrt_T_rec :
forall T1 T2 n1,
  degree_T_wrt_T (S n1) T1 ->
  degree_T_wrt_T n1 T2 ->
  degree_T_wrt_T n1 (open_T_wrt_T_rec n1 T2 T1).
Proof.
pose proof degree_T_wrt_T_open_T_wrt_T_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_T_wrt_T_open_T_wrt_T_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Sc_wrt_T_open_Sc_wrt_T_rec_mutual :
(forall Sc1 T1 n1,
  degree_Sc_wrt_T (S n1) Sc1 ->
  degree_T_wrt_T n1 T1 ->
  degree_Sc_wrt_T n1 (open_Sc_wrt_T_rec n1 T1 Sc1)).
Proof.
apply_mutual_ind Sc_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_Sc_wrt_T_open_Sc_wrt_T_rec :
forall Sc1 T1 n1,
  degree_Sc_wrt_T (S n1) Sc1 ->
  degree_T_wrt_T n1 T1 ->
  degree_Sc_wrt_T n1 (open_Sc_wrt_T_rec n1 T1 Sc1).
Proof.
pose proof degree_Sc_wrt_T_open_Sc_wrt_T_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_Sc_wrt_T_open_Sc_wrt_T_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Tm_wrt_T_open_Tm_wrt_T_rec_mutual :
(forall t1 T1 n1,
  degree_Tm_wrt_T (S n1) t1 ->
  degree_T_wrt_T n1 T1 ->
  degree_Tm_wrt_T n1 (open_Tm_wrt_T_rec n1 T1 t1)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_Tm_wrt_T_open_Tm_wrt_T_rec :
forall t1 T1 n1,
  degree_Tm_wrt_T (S n1) t1 ->
  degree_T_wrt_T n1 T1 ->
  degree_Tm_wrt_T n1 (open_Tm_wrt_T_rec n1 T1 t1).
Proof.
pose proof degree_Tm_wrt_T_open_Tm_wrt_T_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_Tm_wrt_T_open_Tm_wrt_T_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Tm_wrt_T_open_Tm_wrt_Tm_rec_mutual :
(forall t1 t2 n1 n2,
  degree_Tm_wrt_T n1 t1 ->
  degree_Tm_wrt_T n1 t2 ->
  degree_Tm_wrt_T n1 (open_Tm_wrt_Tm_rec n2 t2 t1)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_Tm_wrt_T_open_Tm_wrt_Tm_rec :
forall t1 t2 n1 n2,
  degree_Tm_wrt_T n1 t1 ->
  degree_Tm_wrt_T n1 t2 ->
  degree_Tm_wrt_T n1 (open_Tm_wrt_Tm_rec n2 t2 t1).
Proof.
pose proof degree_Tm_wrt_T_open_Tm_wrt_Tm_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_Tm_wrt_T_open_Tm_wrt_Tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Tm_wrt_Tm_open_Tm_wrt_T_rec_mutual :
(forall t1 T1 n1 n2,
  degree_Tm_wrt_Tm n1 t1 ->
  degree_Tm_wrt_Tm n1 (open_Tm_wrt_T_rec n2 T1 t1)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_Tm_wrt_Tm_open_Tm_wrt_T_rec :
forall t1 T1 n1 n2,
  degree_Tm_wrt_Tm n1 t1 ->
  degree_Tm_wrt_Tm n1 (open_Tm_wrt_T_rec n2 T1 t1).
Proof.
pose proof degree_Tm_wrt_Tm_open_Tm_wrt_T_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_Tm_wrt_Tm_open_Tm_wrt_T_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Tm_wrt_Tm_open_Tm_wrt_Tm_rec_mutual :
(forall t1 t2 n1,
  degree_Tm_wrt_Tm (S n1) t1 ->
  degree_Tm_wrt_Tm n1 t2 ->
  degree_Tm_wrt_Tm n1 (open_Tm_wrt_Tm_rec n1 t2 t1)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_Tm_wrt_Tm_open_Tm_wrt_Tm_rec :
forall t1 t2 n1,
  degree_Tm_wrt_Tm (S n1) t1 ->
  degree_Tm_wrt_Tm n1 t2 ->
  degree_Tm_wrt_Tm n1 (open_Tm_wrt_Tm_rec n1 t2 t1).
Proof.
pose proof degree_Tm_wrt_Tm_open_Tm_wrt_Tm_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_Tm_wrt_Tm_open_Tm_wrt_Tm_rec : lngen.

(* end hide *)

Lemma degree_Ex_wrt_Ex_open_Ex_wrt_Ex :
forall e1 e2,
  degree_Ex_wrt_Ex 1 e1 ->
  degree_Ex_wrt_Ex 0 e2 ->
  degree_Ex_wrt_Ex 0 (open_Ex_wrt_Ex e1 e2).
Proof.
unfold open_Ex_wrt_Ex; default_simp.
Qed.

#[export] Hint Resolve degree_Ex_wrt_Ex_open_Ex_wrt_Ex : lngen.

Lemma degree_T_wrt_T_open_T_wrt_T :
forall T1 T2,
  degree_T_wrt_T 1 T1 ->
  degree_T_wrt_T 0 T2 ->
  degree_T_wrt_T 0 (open_T_wrt_T T1 T2).
Proof.
unfold open_T_wrt_T; default_simp.
Qed.

#[export] Hint Resolve degree_T_wrt_T_open_T_wrt_T : lngen.

Lemma degree_Sc_wrt_T_open_Sc_wrt_T :
forall Sc1 T1,
  degree_Sc_wrt_T 1 Sc1 ->
  degree_T_wrt_T 0 T1 ->
  degree_Sc_wrt_T 0 (open_Sc_wrt_T Sc1 T1).
Proof.
unfold open_Sc_wrt_T; default_simp.
Qed.

#[export] Hint Resolve degree_Sc_wrt_T_open_Sc_wrt_T : lngen.

Lemma degree_Tm_wrt_T_open_Tm_wrt_T :
forall t1 T1,
  degree_Tm_wrt_T 1 t1 ->
  degree_T_wrt_T 0 T1 ->
  degree_Tm_wrt_T 0 (open_Tm_wrt_T t1 T1).
Proof.
unfold open_Tm_wrt_T; default_simp.
Qed.

#[export] Hint Resolve degree_Tm_wrt_T_open_Tm_wrt_T : lngen.

Lemma degree_Tm_wrt_T_open_Tm_wrt_Tm :
forall t1 t2 n1,
  degree_Tm_wrt_T n1 t1 ->
  degree_Tm_wrt_T n1 t2 ->
  degree_Tm_wrt_T n1 (open_Tm_wrt_Tm t1 t2).
Proof.
unfold open_Tm_wrt_Tm; default_simp.
Qed.

#[export] Hint Resolve degree_Tm_wrt_T_open_Tm_wrt_Tm : lngen.

Lemma degree_Tm_wrt_Tm_open_Tm_wrt_T :
forall t1 T1 n1,
  degree_Tm_wrt_Tm n1 t1 ->
  degree_Tm_wrt_Tm n1 (open_Tm_wrt_T t1 T1).
Proof.
unfold open_Tm_wrt_T; default_simp.
Qed.

#[export] Hint Resolve degree_Tm_wrt_Tm_open_Tm_wrt_T : lngen.

Lemma degree_Tm_wrt_Tm_open_Tm_wrt_Tm :
forall t1 t2,
  degree_Tm_wrt_Tm 1 t1 ->
  degree_Tm_wrt_Tm 0 t2 ->
  degree_Tm_wrt_Tm 0 (open_Tm_wrt_Tm t1 t2).
Proof.
unfold open_Tm_wrt_Tm; default_simp.
Qed.

#[export] Hint Resolve degree_Tm_wrt_Tm_open_Tm_wrt_Tm : lngen.

(* begin hide *)

Lemma degree_Ex_wrt_Ex_open_Ex_wrt_Ex_rec_inv_mutual :
(forall e1 e2 n1,
  degree_Ex_wrt_Ex n1 (open_Ex_wrt_Ex_rec n1 e2 e1) ->
  degree_Ex_wrt_Ex (S n1) e1).
Proof.
apply_mutual_ind Ex_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_Ex_wrt_Ex_open_Ex_wrt_Ex_rec_inv :
forall e1 e2 n1,
  degree_Ex_wrt_Ex n1 (open_Ex_wrt_Ex_rec n1 e2 e1) ->
  degree_Ex_wrt_Ex (S n1) e1.
Proof.
pose proof degree_Ex_wrt_Ex_open_Ex_wrt_Ex_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_Ex_wrt_Ex_open_Ex_wrt_Ex_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_T_wrt_T_open_T_wrt_T_rec_inv_mutual :
(forall T1 T2 n1,
  degree_T_wrt_T n1 (open_T_wrt_T_rec n1 T2 T1) ->
  degree_T_wrt_T (S n1) T1).
Proof.
apply_mutual_ind T_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_T_wrt_T_open_T_wrt_T_rec_inv :
forall T1 T2 n1,
  degree_T_wrt_T n1 (open_T_wrt_T_rec n1 T2 T1) ->
  degree_T_wrt_T (S n1) T1.
Proof.
pose proof degree_T_wrt_T_open_T_wrt_T_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_T_wrt_T_open_T_wrt_T_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Sc_wrt_T_open_Sc_wrt_T_rec_inv_mutual :
(forall Sc1 T1 n1,
  degree_Sc_wrt_T n1 (open_Sc_wrt_T_rec n1 T1 Sc1) ->
  degree_Sc_wrt_T (S n1) Sc1).
Proof.
apply_mutual_ind Sc_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_Sc_wrt_T_open_Sc_wrt_T_rec_inv :
forall Sc1 T1 n1,
  degree_Sc_wrt_T n1 (open_Sc_wrt_T_rec n1 T1 Sc1) ->
  degree_Sc_wrt_T (S n1) Sc1.
Proof.
pose proof degree_Sc_wrt_T_open_Sc_wrt_T_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_Sc_wrt_T_open_Sc_wrt_T_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Tm_wrt_T_open_Tm_wrt_T_rec_inv_mutual :
(forall t1 T1 n1,
  degree_Tm_wrt_T n1 (open_Tm_wrt_T_rec n1 T1 t1) ->
  degree_Tm_wrt_T (S n1) t1).
Proof.
apply_mutual_ind Tm_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_Tm_wrt_T_open_Tm_wrt_T_rec_inv :
forall t1 T1 n1,
  degree_Tm_wrt_T n1 (open_Tm_wrt_T_rec n1 T1 t1) ->
  degree_Tm_wrt_T (S n1) t1.
Proof.
pose proof degree_Tm_wrt_T_open_Tm_wrt_T_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_Tm_wrt_T_open_Tm_wrt_T_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Tm_wrt_T_open_Tm_wrt_Tm_rec_inv_mutual :
(forall t1 t2 n1 n2,
  degree_Tm_wrt_T n1 (open_Tm_wrt_Tm_rec n2 t2 t1) ->
  degree_Tm_wrt_T n1 t1).
Proof.
apply_mutual_ind Tm_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_Tm_wrt_T_open_Tm_wrt_Tm_rec_inv :
forall t1 t2 n1 n2,
  degree_Tm_wrt_T n1 (open_Tm_wrt_Tm_rec n2 t2 t1) ->
  degree_Tm_wrt_T n1 t1.
Proof.
pose proof degree_Tm_wrt_T_open_Tm_wrt_Tm_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_Tm_wrt_T_open_Tm_wrt_Tm_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Tm_wrt_Tm_open_Tm_wrt_T_rec_inv_mutual :
(forall t1 T1 n1 n2,
  degree_Tm_wrt_Tm n1 (open_Tm_wrt_T_rec n2 T1 t1) ->
  degree_Tm_wrt_Tm n1 t1).
Proof.
apply_mutual_ind Tm_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_Tm_wrt_Tm_open_Tm_wrt_T_rec_inv :
forall t1 T1 n1 n2,
  degree_Tm_wrt_Tm n1 (open_Tm_wrt_T_rec n2 T1 t1) ->
  degree_Tm_wrt_Tm n1 t1.
Proof.
pose proof degree_Tm_wrt_Tm_open_Tm_wrt_T_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_Tm_wrt_Tm_open_Tm_wrt_T_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Tm_wrt_Tm_open_Tm_wrt_Tm_rec_inv_mutual :
(forall t1 t2 n1,
  degree_Tm_wrt_Tm n1 (open_Tm_wrt_Tm_rec n1 t2 t1) ->
  degree_Tm_wrt_Tm (S n1) t1).
Proof.
apply_mutual_ind Tm_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_Tm_wrt_Tm_open_Tm_wrt_Tm_rec_inv :
forall t1 t2 n1,
  degree_Tm_wrt_Tm n1 (open_Tm_wrt_Tm_rec n1 t2 t1) ->
  degree_Tm_wrt_Tm (S n1) t1.
Proof.
pose proof degree_Tm_wrt_Tm_open_Tm_wrt_Tm_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_Tm_wrt_Tm_open_Tm_wrt_Tm_rec_inv : lngen.

(* end hide *)

Lemma degree_Ex_wrt_Ex_open_Ex_wrt_Ex_inv :
forall e1 e2,
  degree_Ex_wrt_Ex 0 (open_Ex_wrt_Ex e1 e2) ->
  degree_Ex_wrt_Ex 1 e1.
Proof.
unfold open_Ex_wrt_Ex; eauto with lngen.
Qed.

#[export] Hint Immediate degree_Ex_wrt_Ex_open_Ex_wrt_Ex_inv : lngen.

Lemma degree_T_wrt_T_open_T_wrt_T_inv :
forall T1 T2,
  degree_T_wrt_T 0 (open_T_wrt_T T1 T2) ->
  degree_T_wrt_T 1 T1.
Proof.
unfold open_T_wrt_T; eauto with lngen.
Qed.

#[export] Hint Immediate degree_T_wrt_T_open_T_wrt_T_inv : lngen.

Lemma degree_Sc_wrt_T_open_Sc_wrt_T_inv :
forall Sc1 T1,
  degree_Sc_wrt_T 0 (open_Sc_wrt_T Sc1 T1) ->
  degree_Sc_wrt_T 1 Sc1.
Proof.
unfold open_Sc_wrt_T; eauto with lngen.
Qed.

#[export] Hint Immediate degree_Sc_wrt_T_open_Sc_wrt_T_inv : lngen.

Lemma degree_Tm_wrt_T_open_Tm_wrt_T_inv :
forall t1 T1,
  degree_Tm_wrt_T 0 (open_Tm_wrt_T t1 T1) ->
  degree_Tm_wrt_T 1 t1.
Proof.
unfold open_Tm_wrt_T; eauto with lngen.
Qed.

#[export] Hint Immediate degree_Tm_wrt_T_open_Tm_wrt_T_inv : lngen.

Lemma degree_Tm_wrt_T_open_Tm_wrt_Tm_inv :
forall t1 t2 n1,
  degree_Tm_wrt_T n1 (open_Tm_wrt_Tm t1 t2) ->
  degree_Tm_wrt_T n1 t1.
Proof.
unfold open_Tm_wrt_Tm; eauto with lngen.
Qed.

#[export] Hint Immediate degree_Tm_wrt_T_open_Tm_wrt_Tm_inv : lngen.

Lemma degree_Tm_wrt_Tm_open_Tm_wrt_T_inv :
forall t1 T1 n1,
  degree_Tm_wrt_Tm n1 (open_Tm_wrt_T t1 T1) ->
  degree_Tm_wrt_Tm n1 t1.
Proof.
unfold open_Tm_wrt_T; eauto with lngen.
Qed.

#[export] Hint Immediate degree_Tm_wrt_Tm_open_Tm_wrt_T_inv : lngen.

Lemma degree_Tm_wrt_Tm_open_Tm_wrt_Tm_inv :
forall t1 t2,
  degree_Tm_wrt_Tm 0 (open_Tm_wrt_Tm t1 t2) ->
  degree_Tm_wrt_Tm 1 t1.
Proof.
unfold open_Tm_wrt_Tm; eauto with lngen.
Qed.

#[export] Hint Immediate degree_Tm_wrt_Tm_open_Tm_wrt_Tm_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_Ex_wrt_Ex_rec_inj_mutual :
(forall e1 e2 x1 n1,
  close_Ex_wrt_Ex_rec n1 x1 e1 = close_Ex_wrt_Ex_rec n1 x1 e2 ->
  e1 = e2).
Proof.
apply_mutual_ind Ex_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_Ex_wrt_Ex_rec_inj :
forall e1 e2 x1 n1,
  close_Ex_wrt_Ex_rec n1 x1 e1 = close_Ex_wrt_Ex_rec n1 x1 e2 ->
  e1 = e2.
Proof.
pose proof close_Ex_wrt_Ex_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_Ex_wrt_Ex_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_T_wrt_T_rec_inj_mutual :
(forall T1 T2 beta1 n1,
  close_T_wrt_T_rec n1 beta1 T1 = close_T_wrt_T_rec n1 beta1 T2 ->
  T1 = T2).
Proof.
apply_mutual_ind T_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_T_wrt_T_rec_inj :
forall T1 T2 beta1 n1,
  close_T_wrt_T_rec n1 beta1 T1 = close_T_wrt_T_rec n1 beta1 T2 ->
  T1 = T2.
Proof.
pose proof close_T_wrt_T_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_T_wrt_T_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_Sc_wrt_T_rec_inj_mutual :
(forall Sc1 Sc2 beta1 n1,
  close_Sc_wrt_T_rec n1 beta1 Sc1 = close_Sc_wrt_T_rec n1 beta1 Sc2 ->
  Sc1 = Sc2).
Proof.
apply_mutual_ind Sc_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_Sc_wrt_T_rec_inj :
forall Sc1 Sc2 beta1 n1,
  close_Sc_wrt_T_rec n1 beta1 Sc1 = close_Sc_wrt_T_rec n1 beta1 Sc2 ->
  Sc1 = Sc2.
Proof.
pose proof close_Sc_wrt_T_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_Sc_wrt_T_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_Tm_wrt_T_rec_inj_mutual :
(forall t1 t2 beta1 n1,
  close_Tm_wrt_T_rec n1 beta1 t1 = close_Tm_wrt_T_rec n1 beta1 t2 ->
  t1 = t2).
Proof.
apply_mutual_ind Tm_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_Tm_wrt_T_rec_inj :
forall t1 t2 beta1 n1,
  close_Tm_wrt_T_rec n1 beta1 t1 = close_Tm_wrt_T_rec n1 beta1 t2 ->
  t1 = t2.
Proof.
pose proof close_Tm_wrt_T_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_Tm_wrt_T_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_Tm_wrt_Tm_rec_inj_mutual :
(forall t1 t2 tx1 n1,
  close_Tm_wrt_Tm_rec n1 tx1 t1 = close_Tm_wrt_Tm_rec n1 tx1 t2 ->
  t1 = t2).
Proof.
apply_mutual_ind Tm_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_Tm_wrt_Tm_rec_inj :
forall t1 t2 tx1 n1,
  close_Tm_wrt_Tm_rec n1 tx1 t1 = close_Tm_wrt_Tm_rec n1 tx1 t2 ->
  t1 = t2.
Proof.
pose proof close_Tm_wrt_Tm_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_Tm_wrt_Tm_rec_inj : lngen.

(* end hide *)

Lemma close_Ex_wrt_Ex_inj :
forall e1 e2 x1,
  close_Ex_wrt_Ex x1 e1 = close_Ex_wrt_Ex x1 e2 ->
  e1 = e2.
Proof.
unfold close_Ex_wrt_Ex; eauto with lngen.
Qed.

#[export] Hint Immediate close_Ex_wrt_Ex_inj : lngen.

Lemma close_T_wrt_T_inj :
forall T1 T2 beta1,
  close_T_wrt_T beta1 T1 = close_T_wrt_T beta1 T2 ->
  T1 = T2.
Proof.
unfold close_T_wrt_T; eauto with lngen.
Qed.

#[export] Hint Immediate close_T_wrt_T_inj : lngen.

Lemma close_Sc_wrt_T_inj :
forall Sc1 Sc2 beta1,
  close_Sc_wrt_T beta1 Sc1 = close_Sc_wrt_T beta1 Sc2 ->
  Sc1 = Sc2.
Proof.
unfold close_Sc_wrt_T; eauto with lngen.
Qed.

#[export] Hint Immediate close_Sc_wrt_T_inj : lngen.

Lemma close_Tm_wrt_T_inj :
forall t1 t2 beta1,
  close_Tm_wrt_T beta1 t1 = close_Tm_wrt_T beta1 t2 ->
  t1 = t2.
Proof.
unfold close_Tm_wrt_T; eauto with lngen.
Qed.

#[export] Hint Immediate close_Tm_wrt_T_inj : lngen.

Lemma close_Tm_wrt_Tm_inj :
forall t1 t2 tx1,
  close_Tm_wrt_Tm tx1 t1 = close_Tm_wrt_Tm tx1 t2 ->
  t1 = t2.
Proof.
unfold close_Tm_wrt_Tm; eauto with lngen.
Qed.

#[export] Hint Immediate close_Tm_wrt_Tm_inj : lngen.

(* begin hide *)

Lemma close_Ex_wrt_Ex_rec_open_Ex_wrt_Ex_rec_mutual :
(forall e1 x1 n1,
  x1 `notin` fv_Ex e1 ->
  close_Ex_wrt_Ex_rec n1 x1 (open_Ex_wrt_Ex_rec n1 (e__Var_f x1) e1) = e1).
Proof.
apply_mutual_ind Ex_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_Ex_wrt_Ex_rec_open_Ex_wrt_Ex_rec :
forall e1 x1 n1,
  x1 `notin` fv_Ex e1 ->
  close_Ex_wrt_Ex_rec n1 x1 (open_Ex_wrt_Ex_rec n1 (e__Var_f x1) e1) = e1.
Proof.
pose proof close_Ex_wrt_Ex_rec_open_Ex_wrt_Ex_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_Ex_wrt_Ex_rec_open_Ex_wrt_Ex_rec : lngen.
#[export] Hint Rewrite close_Ex_wrt_Ex_rec_open_Ex_wrt_Ex_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_T_wrt_T_rec_open_T_wrt_T_rec_mutual :
(forall T1 beta1 n1,
  beta1 `notin` fsk_T T1 ->
  close_T_wrt_T_rec n1 beta1 (open_T_wrt_T_rec n1 (T__Var_f beta1) T1) = T1).
Proof.
apply_mutual_ind T_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_T_wrt_T_rec_open_T_wrt_T_rec :
forall T1 beta1 n1,
  beta1 `notin` fsk_T T1 ->
  close_T_wrt_T_rec n1 beta1 (open_T_wrt_T_rec n1 (T__Var_f beta1) T1) = T1.
Proof.
pose proof close_T_wrt_T_rec_open_T_wrt_T_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_T_wrt_T_rec_open_T_wrt_T_rec : lngen.
#[export] Hint Rewrite close_T_wrt_T_rec_open_T_wrt_T_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_Sc_wrt_T_rec_open_Sc_wrt_T_rec_mutual :
(forall Sc1 beta1 n1,
  beta1 `notin` fsk_Sc Sc1 ->
  close_Sc_wrt_T_rec n1 beta1 (open_Sc_wrt_T_rec n1 (T__Var_f beta1) Sc1) = Sc1).
Proof.
apply_mutual_ind Sc_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_Sc_wrt_T_rec_open_Sc_wrt_T_rec :
forall Sc1 beta1 n1,
  beta1 `notin` fsk_Sc Sc1 ->
  close_Sc_wrt_T_rec n1 beta1 (open_Sc_wrt_T_rec n1 (T__Var_f beta1) Sc1) = Sc1.
Proof.
pose proof close_Sc_wrt_T_rec_open_Sc_wrt_T_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_Sc_wrt_T_rec_open_Sc_wrt_T_rec : lngen.
#[export] Hint Rewrite close_Sc_wrt_T_rec_open_Sc_wrt_T_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_Tm_wrt_T_rec_open_Tm_wrt_T_rec_mutual :
(forall t1 beta1 n1,
  beta1 `notin` fsk_Tm t1 ->
  close_Tm_wrt_T_rec n1 beta1 (open_Tm_wrt_T_rec n1 (T__Var_f beta1) t1) = t1).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_Tm_wrt_T_rec_open_Tm_wrt_T_rec :
forall t1 beta1 n1,
  beta1 `notin` fsk_Tm t1 ->
  close_Tm_wrt_T_rec n1 beta1 (open_Tm_wrt_T_rec n1 (T__Var_f beta1) t1) = t1.
Proof.
pose proof close_Tm_wrt_T_rec_open_Tm_wrt_T_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_Tm_wrt_T_rec_open_Tm_wrt_T_rec : lngen.
#[export] Hint Rewrite close_Tm_wrt_T_rec_open_Tm_wrt_T_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_Tm_wrt_Tm_rec_open_Tm_wrt_Tm_rec_mutual :
(forall t1 tx1 n1,
  tx1 `notin` ftv_Tm t1 ->
  close_Tm_wrt_Tm_rec n1 tx1 (open_Tm_wrt_Tm_rec n1 (t__Var_f tx1) t1) = t1).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_Tm_wrt_Tm_rec_open_Tm_wrt_Tm_rec :
forall t1 tx1 n1,
  tx1 `notin` ftv_Tm t1 ->
  close_Tm_wrt_Tm_rec n1 tx1 (open_Tm_wrt_Tm_rec n1 (t__Var_f tx1) t1) = t1.
Proof.
pose proof close_Tm_wrt_Tm_rec_open_Tm_wrt_Tm_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_Tm_wrt_Tm_rec_open_Tm_wrt_Tm_rec : lngen.
#[export] Hint Rewrite close_Tm_wrt_Tm_rec_open_Tm_wrt_Tm_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_Ex_wrt_Ex_open_Ex_wrt_Ex :
forall e1 x1,
  x1 `notin` fv_Ex e1 ->
  close_Ex_wrt_Ex x1 (open_Ex_wrt_Ex e1 (e__Var_f x1)) = e1.
Proof.
unfold close_Ex_wrt_Ex; unfold open_Ex_wrt_Ex; default_simp.
Qed.

#[export] Hint Resolve close_Ex_wrt_Ex_open_Ex_wrt_Ex : lngen.
#[export] Hint Rewrite close_Ex_wrt_Ex_open_Ex_wrt_Ex using solve [auto] : lngen.

Lemma close_T_wrt_T_open_T_wrt_T :
forall T1 beta1,
  beta1 `notin` fsk_T T1 ->
  close_T_wrt_T beta1 (open_T_wrt_T T1 (T__Var_f beta1)) = T1.
Proof.
unfold close_T_wrt_T; unfold open_T_wrt_T; default_simp.
Qed.

#[export] Hint Resolve close_T_wrt_T_open_T_wrt_T : lngen.
#[export] Hint Rewrite close_T_wrt_T_open_T_wrt_T using solve [auto] : lngen.

Lemma close_Sc_wrt_T_open_Sc_wrt_T :
forall Sc1 beta1,
  beta1 `notin` fsk_Sc Sc1 ->
  close_Sc_wrt_T beta1 (open_Sc_wrt_T Sc1 (T__Var_f beta1)) = Sc1.
Proof.
unfold close_Sc_wrt_T; unfold open_Sc_wrt_T; default_simp.
Qed.

#[export] Hint Resolve close_Sc_wrt_T_open_Sc_wrt_T : lngen.
#[export] Hint Rewrite close_Sc_wrt_T_open_Sc_wrt_T using solve [auto] : lngen.

Lemma close_Tm_wrt_T_open_Tm_wrt_T :
forall t1 beta1,
  beta1 `notin` fsk_Tm t1 ->
  close_Tm_wrt_T beta1 (open_Tm_wrt_T t1 (T__Var_f beta1)) = t1.
Proof.
unfold close_Tm_wrt_T; unfold open_Tm_wrt_T; default_simp.
Qed.

#[export] Hint Resolve close_Tm_wrt_T_open_Tm_wrt_T : lngen.
#[export] Hint Rewrite close_Tm_wrt_T_open_Tm_wrt_T using solve [auto] : lngen.

Lemma close_Tm_wrt_Tm_open_Tm_wrt_Tm :
forall t1 tx1,
  tx1 `notin` ftv_Tm t1 ->
  close_Tm_wrt_Tm tx1 (open_Tm_wrt_Tm t1 (t__Var_f tx1)) = t1.
Proof.
unfold close_Tm_wrt_Tm; unfold open_Tm_wrt_Tm; default_simp.
Qed.

#[export] Hint Resolve close_Tm_wrt_Tm_open_Tm_wrt_Tm : lngen.
#[export] Hint Rewrite close_Tm_wrt_Tm_open_Tm_wrt_Tm using solve [auto] : lngen.

(* begin hide *)

Lemma open_Ex_wrt_Ex_rec_close_Ex_wrt_Ex_rec_mutual :
(forall e1 x1 n1,
  open_Ex_wrt_Ex_rec n1 (e__Var_f x1) (close_Ex_wrt_Ex_rec n1 x1 e1) = e1).
Proof.
apply_mutual_ind Ex_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_Ex_wrt_Ex_rec_close_Ex_wrt_Ex_rec :
forall e1 x1 n1,
  open_Ex_wrt_Ex_rec n1 (e__Var_f x1) (close_Ex_wrt_Ex_rec n1 x1 e1) = e1.
Proof.
pose proof open_Ex_wrt_Ex_rec_close_Ex_wrt_Ex_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_Ex_wrt_Ex_rec_close_Ex_wrt_Ex_rec : lngen.
#[export] Hint Rewrite open_Ex_wrt_Ex_rec_close_Ex_wrt_Ex_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_T_wrt_T_rec_close_T_wrt_T_rec_mutual :
(forall T1 beta1 n1,
  open_T_wrt_T_rec n1 (T__Var_f beta1) (close_T_wrt_T_rec n1 beta1 T1) = T1).
Proof.
apply_mutual_ind T_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_T_wrt_T_rec_close_T_wrt_T_rec :
forall T1 beta1 n1,
  open_T_wrt_T_rec n1 (T__Var_f beta1) (close_T_wrt_T_rec n1 beta1 T1) = T1.
Proof.
pose proof open_T_wrt_T_rec_close_T_wrt_T_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_T_wrt_T_rec_close_T_wrt_T_rec : lngen.
#[export] Hint Rewrite open_T_wrt_T_rec_close_T_wrt_T_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_Sc_wrt_T_rec_close_Sc_wrt_T_rec_mutual :
(forall Sc1 beta1 n1,
  open_Sc_wrt_T_rec n1 (T__Var_f beta1) (close_Sc_wrt_T_rec n1 beta1 Sc1) = Sc1).
Proof.
apply_mutual_ind Sc_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_Sc_wrt_T_rec_close_Sc_wrt_T_rec :
forall Sc1 beta1 n1,
  open_Sc_wrt_T_rec n1 (T__Var_f beta1) (close_Sc_wrt_T_rec n1 beta1 Sc1) = Sc1.
Proof.
pose proof open_Sc_wrt_T_rec_close_Sc_wrt_T_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_Sc_wrt_T_rec_close_Sc_wrt_T_rec : lngen.
#[export] Hint Rewrite open_Sc_wrt_T_rec_close_Sc_wrt_T_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_Tm_wrt_T_rec_close_Tm_wrt_T_rec_mutual :
(forall t1 beta1 n1,
  open_Tm_wrt_T_rec n1 (T__Var_f beta1) (close_Tm_wrt_T_rec n1 beta1 t1) = t1).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_Tm_wrt_T_rec_close_Tm_wrt_T_rec :
forall t1 beta1 n1,
  open_Tm_wrt_T_rec n1 (T__Var_f beta1) (close_Tm_wrt_T_rec n1 beta1 t1) = t1.
Proof.
pose proof open_Tm_wrt_T_rec_close_Tm_wrt_T_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_Tm_wrt_T_rec_close_Tm_wrt_T_rec : lngen.
#[export] Hint Rewrite open_Tm_wrt_T_rec_close_Tm_wrt_T_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_Tm_wrt_Tm_rec_close_Tm_wrt_Tm_rec_mutual :
(forall t1 tx1 n1,
  open_Tm_wrt_Tm_rec n1 (t__Var_f tx1) (close_Tm_wrt_Tm_rec n1 tx1 t1) = t1).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_Tm_wrt_Tm_rec_close_Tm_wrt_Tm_rec :
forall t1 tx1 n1,
  open_Tm_wrt_Tm_rec n1 (t__Var_f tx1) (close_Tm_wrt_Tm_rec n1 tx1 t1) = t1.
Proof.
pose proof open_Tm_wrt_Tm_rec_close_Tm_wrt_Tm_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_Tm_wrt_Tm_rec_close_Tm_wrt_Tm_rec : lngen.
#[export] Hint Rewrite open_Tm_wrt_Tm_rec_close_Tm_wrt_Tm_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_Ex_wrt_Ex_close_Ex_wrt_Ex :
forall e1 x1,
  open_Ex_wrt_Ex (close_Ex_wrt_Ex x1 e1) (e__Var_f x1) = e1.
Proof.
unfold close_Ex_wrt_Ex; unfold open_Ex_wrt_Ex; default_simp.
Qed.

#[export] Hint Resolve open_Ex_wrt_Ex_close_Ex_wrt_Ex : lngen.
#[export] Hint Rewrite open_Ex_wrt_Ex_close_Ex_wrt_Ex using solve [auto] : lngen.

Lemma open_T_wrt_T_close_T_wrt_T :
forall T1 beta1,
  open_T_wrt_T (close_T_wrt_T beta1 T1) (T__Var_f beta1) = T1.
Proof.
unfold close_T_wrt_T; unfold open_T_wrt_T; default_simp.
Qed.

#[export] Hint Resolve open_T_wrt_T_close_T_wrt_T : lngen.
#[export] Hint Rewrite open_T_wrt_T_close_T_wrt_T using solve [auto] : lngen.

Lemma open_Sc_wrt_T_close_Sc_wrt_T :
forall Sc1 beta1,
  open_Sc_wrt_T (close_Sc_wrt_T beta1 Sc1) (T__Var_f beta1) = Sc1.
Proof.
unfold close_Sc_wrt_T; unfold open_Sc_wrt_T; default_simp.
Qed.

#[export] Hint Resolve open_Sc_wrt_T_close_Sc_wrt_T : lngen.
#[export] Hint Rewrite open_Sc_wrt_T_close_Sc_wrt_T using solve [auto] : lngen.

Lemma open_Tm_wrt_T_close_Tm_wrt_T :
forall t1 beta1,
  open_Tm_wrt_T (close_Tm_wrt_T beta1 t1) (T__Var_f beta1) = t1.
Proof.
unfold close_Tm_wrt_T; unfold open_Tm_wrt_T; default_simp.
Qed.

#[export] Hint Resolve open_Tm_wrt_T_close_Tm_wrt_T : lngen.
#[export] Hint Rewrite open_Tm_wrt_T_close_Tm_wrt_T using solve [auto] : lngen.

Lemma open_Tm_wrt_Tm_close_Tm_wrt_Tm :
forall t1 tx1,
  open_Tm_wrt_Tm (close_Tm_wrt_Tm tx1 t1) (t__Var_f tx1) = t1.
Proof.
unfold close_Tm_wrt_Tm; unfold open_Tm_wrt_Tm; default_simp.
Qed.

#[export] Hint Resolve open_Tm_wrt_Tm_close_Tm_wrt_Tm : lngen.
#[export] Hint Rewrite open_Tm_wrt_Tm_close_Tm_wrt_Tm using solve [auto] : lngen.

(* begin hide *)

Lemma open_Ex_wrt_Ex_rec_inj_mutual :
(forall e2 e1 x1 n1,
  x1 `notin` fv_Ex e2 ->
  x1 `notin` fv_Ex e1 ->
  open_Ex_wrt_Ex_rec n1 (e__Var_f x1) e2 = open_Ex_wrt_Ex_rec n1 (e__Var_f x1) e1 ->
  e2 = e1).
Proof.
apply_mutual_ind Ex_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_Ex_wrt_Ex_rec_inj :
forall e2 e1 x1 n1,
  x1 `notin` fv_Ex e2 ->
  x1 `notin` fv_Ex e1 ->
  open_Ex_wrt_Ex_rec n1 (e__Var_f x1) e2 = open_Ex_wrt_Ex_rec n1 (e__Var_f x1) e1 ->
  e2 = e1.
Proof.
pose proof open_Ex_wrt_Ex_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_Ex_wrt_Ex_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_T_wrt_T_rec_inj_mutual :
(forall T2 T1 beta1 n1,
  beta1 `notin` fsk_T T2 ->
  beta1 `notin` fsk_T T1 ->
  open_T_wrt_T_rec n1 (T__Var_f beta1) T2 = open_T_wrt_T_rec n1 (T__Var_f beta1) T1 ->
  T2 = T1).
Proof.
apply_mutual_ind T_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_T_wrt_T_rec_inj :
forall T2 T1 beta1 n1,
  beta1 `notin` fsk_T T2 ->
  beta1 `notin` fsk_T T1 ->
  open_T_wrt_T_rec n1 (T__Var_f beta1) T2 = open_T_wrt_T_rec n1 (T__Var_f beta1) T1 ->
  T2 = T1.
Proof.
pose proof open_T_wrt_T_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_T_wrt_T_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_Sc_wrt_T_rec_inj_mutual :
(forall Sc2 Sc1 beta1 n1,
  beta1 `notin` fsk_Sc Sc2 ->
  beta1 `notin` fsk_Sc Sc1 ->
  open_Sc_wrt_T_rec n1 (T__Var_f beta1) Sc2 = open_Sc_wrt_T_rec n1 (T__Var_f beta1) Sc1 ->
  Sc2 = Sc1).
Proof.
apply_mutual_ind Sc_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_Sc_wrt_T_rec_inj :
forall Sc2 Sc1 beta1 n1,
  beta1 `notin` fsk_Sc Sc2 ->
  beta1 `notin` fsk_Sc Sc1 ->
  open_Sc_wrt_T_rec n1 (T__Var_f beta1) Sc2 = open_Sc_wrt_T_rec n1 (T__Var_f beta1) Sc1 ->
  Sc2 = Sc1.
Proof.
pose proof open_Sc_wrt_T_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_Sc_wrt_T_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_Tm_wrt_T_rec_inj_mutual :
(forall t2 t1 beta1 n1,
  beta1 `notin` fsk_Tm t2 ->
  beta1 `notin` fsk_Tm t1 ->
  open_Tm_wrt_T_rec n1 (T__Var_f beta1) t2 = open_Tm_wrt_T_rec n1 (T__Var_f beta1) t1 ->
  t2 = t1).
Proof.
apply_mutual_ind Tm_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_Tm_wrt_T_rec_inj :
forall t2 t1 beta1 n1,
  beta1 `notin` fsk_Tm t2 ->
  beta1 `notin` fsk_Tm t1 ->
  open_Tm_wrt_T_rec n1 (T__Var_f beta1) t2 = open_Tm_wrt_T_rec n1 (T__Var_f beta1) t1 ->
  t2 = t1.
Proof.
pose proof open_Tm_wrt_T_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_Tm_wrt_T_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_Tm_wrt_Tm_rec_inj_mutual :
(forall t2 t1 tx1 n1,
  tx1 `notin` ftv_Tm t2 ->
  tx1 `notin` ftv_Tm t1 ->
  open_Tm_wrt_Tm_rec n1 (t__Var_f tx1) t2 = open_Tm_wrt_Tm_rec n1 (t__Var_f tx1) t1 ->
  t2 = t1).
Proof.
apply_mutual_ind Tm_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_Tm_wrt_Tm_rec_inj :
forall t2 t1 tx1 n1,
  tx1 `notin` ftv_Tm t2 ->
  tx1 `notin` ftv_Tm t1 ->
  open_Tm_wrt_Tm_rec n1 (t__Var_f tx1) t2 = open_Tm_wrt_Tm_rec n1 (t__Var_f tx1) t1 ->
  t2 = t1.
Proof.
pose proof open_Tm_wrt_Tm_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_Tm_wrt_Tm_rec_inj : lngen.

(* end hide *)

Lemma open_Ex_wrt_Ex_inj :
forall e2 e1 x1,
  x1 `notin` fv_Ex e2 ->
  x1 `notin` fv_Ex e1 ->
  open_Ex_wrt_Ex e2 (e__Var_f x1) = open_Ex_wrt_Ex e1 (e__Var_f x1) ->
  e2 = e1.
Proof.
unfold open_Ex_wrt_Ex; eauto with lngen.
Qed.

#[export] Hint Immediate open_Ex_wrt_Ex_inj : lngen.

Lemma open_T_wrt_T_inj :
forall T2 T1 beta1,
  beta1 `notin` fsk_T T2 ->
  beta1 `notin` fsk_T T1 ->
  open_T_wrt_T T2 (T__Var_f beta1) = open_T_wrt_T T1 (T__Var_f beta1) ->
  T2 = T1.
Proof.
unfold open_T_wrt_T; eauto with lngen.
Qed.

#[export] Hint Immediate open_T_wrt_T_inj : lngen.

Lemma open_Sc_wrt_T_inj :
forall Sc2 Sc1 beta1,
  beta1 `notin` fsk_Sc Sc2 ->
  beta1 `notin` fsk_Sc Sc1 ->
  open_Sc_wrt_T Sc2 (T__Var_f beta1) = open_Sc_wrt_T Sc1 (T__Var_f beta1) ->
  Sc2 = Sc1.
Proof.
unfold open_Sc_wrt_T; eauto with lngen.
Qed.

#[export] Hint Immediate open_Sc_wrt_T_inj : lngen.

Lemma open_Tm_wrt_T_inj :
forall t2 t1 beta1,
  beta1 `notin` fsk_Tm t2 ->
  beta1 `notin` fsk_Tm t1 ->
  open_Tm_wrt_T t2 (T__Var_f beta1) = open_Tm_wrt_T t1 (T__Var_f beta1) ->
  t2 = t1.
Proof.
unfold open_Tm_wrt_T; eauto with lngen.
Qed.

#[export] Hint Immediate open_Tm_wrt_T_inj : lngen.

Lemma open_Tm_wrt_Tm_inj :
forall t2 t1 tx1,
  tx1 `notin` ftv_Tm t2 ->
  tx1 `notin` ftv_Tm t1 ->
  open_Tm_wrt_Tm t2 (t__Var_f tx1) = open_Tm_wrt_Tm t1 (t__Var_f tx1) ->
  t2 = t1.
Proof.
unfold open_Tm_wrt_Tm; eauto with lngen.
Qed.

#[export] Hint Immediate open_Tm_wrt_Tm_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_Ex_wrt_Ex_of_lc_Ex_mutual :
(forall e1,
  lc_Ex e1 ->
  degree_Ex_wrt_Ex 0 e1).
Proof.
apply_mutual_ind lc_Ex_mutind;
intros;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_Ex_wrt_Ex_of_lc_Ex :
forall e1,
  lc_Ex e1 ->
  degree_Ex_wrt_Ex 0 e1.
Proof.
pose proof degree_Ex_wrt_Ex_of_lc_Ex_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_Ex_wrt_Ex_of_lc_Ex : lngen.

(* begin hide *)

Lemma degree_T_wrt_T_of_lc_T_mutual :
(forall T1,
  lc_T T1 ->
  degree_T_wrt_T 0 T1).
Proof.
apply_mutual_ind lc_T_mutind;
intros;
let beta1 := fresh "beta1" in pick_fresh beta1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_T_wrt_T_of_lc_T :
forall T1,
  lc_T T1 ->
  degree_T_wrt_T 0 T1.
Proof.
pose proof degree_T_wrt_T_of_lc_T_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_T_wrt_T_of_lc_T : lngen.

(* begin hide *)

Lemma degree_Sc_wrt_T_of_lc_Sc_mutual :
(forall Sc1,
  lc_Sc Sc1 ->
  degree_Sc_wrt_T 0 Sc1).
Proof.
apply_mutual_ind lc_Sc_mutind;
intros;
let beta1 := fresh "beta1" in pick_fresh beta1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_Sc_wrt_T_of_lc_Sc :
forall Sc1,
  lc_Sc Sc1 ->
  degree_Sc_wrt_T 0 Sc1.
Proof.
pose proof degree_Sc_wrt_T_of_lc_Sc_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_Sc_wrt_T_of_lc_Sc : lngen.

(* begin hide *)

Lemma degree_Tm_wrt_T_of_lc_Tm_mutual :
(forall t1,
  lc_Tm t1 ->
  degree_Tm_wrt_T 0 t1).
Proof.
apply_mutual_ind lc_Tm_mutind;
intros;
let beta1 := fresh "beta1" in pick_fresh beta1;
let tx1 := fresh "tx1" in pick_fresh tx1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_Tm_wrt_T_of_lc_Tm :
forall t1,
  lc_Tm t1 ->
  degree_Tm_wrt_T 0 t1.
Proof.
pose proof degree_Tm_wrt_T_of_lc_Tm_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_Tm_wrt_T_of_lc_Tm : lngen.

(* begin hide *)

Lemma degree_Tm_wrt_Tm_of_lc_Tm_mutual :
(forall t1,
  lc_Tm t1 ->
  degree_Tm_wrt_Tm 0 t1).
Proof.
apply_mutual_ind lc_Tm_mutind;
intros;
let beta1 := fresh "beta1" in pick_fresh beta1;
let tx1 := fresh "tx1" in pick_fresh tx1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_Tm_wrt_Tm_of_lc_Tm :
forall t1,
  lc_Tm t1 ->
  degree_Tm_wrt_Tm 0 t1.
Proof.
pose proof degree_Tm_wrt_Tm_of_lc_Tm_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_Tm_wrt_Tm_of_lc_Tm : lngen.

(* begin hide *)

Lemma lc_Ex_of_degree_size_mutual :
forall i1,
(forall e1,
  size_Ex e1 = i1 ->
  degree_Ex_wrt_Ex 0 e1 ->
  lc_Ex e1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind Ex_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_Ex_of_degree :
forall e1,
  degree_Ex_wrt_Ex 0 e1 ->
  lc_Ex e1.
Proof.
intros e1; intros;
pose proof (lc_Ex_of_degree_size_mutual (size_Ex e1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_Ex_of_degree : lngen.

(* begin hide *)

Lemma lc_T_of_degree_size_mutual :
forall i1,
(forall T1,
  size_T T1 = i1 ->
  degree_T_wrt_T 0 T1 ->
  lc_T T1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind T_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_T_of_degree :
forall T1,
  degree_T_wrt_T 0 T1 ->
  lc_T T1.
Proof.
intros T1; intros;
pose proof (lc_T_of_degree_size_mutual (size_T T1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_T_of_degree : lngen.

(* begin hide *)

Lemma lc_Sc_of_degree_size_mutual :
forall i1,
(forall Sc1,
  size_Sc Sc1 = i1 ->
  degree_Sc_wrt_T 0 Sc1 ->
  lc_Sc Sc1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind Sc_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_Sc_of_degree :
forall Sc1,
  degree_Sc_wrt_T 0 Sc1 ->
  lc_Sc Sc1.
Proof.
intros Sc1; intros;
pose proof (lc_Sc_of_degree_size_mutual (size_Sc Sc1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_Sc_of_degree : lngen.

(* begin hide *)

Lemma lc_Tm_of_degree_size_mutual :
forall i1,
(forall t1,
  size_Tm t1 = i1 ->
  degree_Tm_wrt_T 0 t1 ->
  degree_Tm_wrt_Tm 0 t1 ->
  lc_Tm t1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind Tm_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_Tm_of_degree :
forall t1,
  degree_Tm_wrt_T 0 t1 ->
  degree_Tm_wrt_Tm 0 t1 ->
  lc_Tm t1.
Proof.
intros t1; intros;
pose proof (lc_Tm_of_degree_size_mutual (size_Tm t1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_Tm_of_degree : lngen.

Ltac Ex_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_Ex_wrt_Ex_of_lc_Ex in J1; clear H
          end).

Ltac T_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_T_wrt_T_of_lc_T in J1; clear H
          end).

Ltac Sc_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_Sc_wrt_T_of_lc_Sc in J1; clear H
          end).

Ltac Tm_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_Tm_wrt_T_of_lc_Tm in J1;
              let J2 := fresh in pose proof H as J2; apply degree_Tm_wrt_Tm_of_lc_Tm in J2; clear H
          end).

Lemma lc_e__Lam_exists :
forall x1 e1,
  lc_Ex (open_Ex_wrt_Ex e1 (e__Var_f x1)) ->
  lc_Ex (e__Lam e1).
Proof.
intros; Ex_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_e__Let_exists :
forall x1 e1 e2,
  lc_Ex e1 ->
  lc_Ex (open_Ex_wrt_Ex e2 (e__Var_f x1)) ->
  lc_Ex (e__Let e1 e2).
Proof.
intros; Ex_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_S__Forall_exists :
forall alpha1 sigma1,
  lc_Sc (open_Sc_wrt_T sigma1 (T__Var_f alpha1)) ->
  lc_Sc (S__Forall sigma1).
Proof.
intros; Sc_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_t__Lam_exists :
forall tx1 tau1 t1,
  lc_T tau1 ->
  lc_Tm (open_Tm_wrt_Tm t1 (t__Var_f tx1)) ->
  lc_Tm (t__Lam tau1 t1).
Proof.
intros; Tm_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_t__TLam_exists :
forall alpha1 t1,
  lc_Tm (open_Tm_wrt_T t1 (T__Var_f alpha1)) ->
  lc_Tm (t__TLam t1).
Proof.
intros; Tm_lc_exists_tac; eauto 6 with lngen.
Qed.

#[export] Hint Extern 1 (lc_Ex (e__Lam _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_e__Lam_exists x1) : core.

#[export] Hint Extern 1 (lc_Ex (e__Let _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_e__Let_exists x1) : core.

#[export] Hint Extern 1 (lc_Sc (S__Forall _)) =>
  let alpha1 := fresh in
  pick_fresh alpha1;
  apply (lc_S__Forall_exists alpha1) : core.

#[export] Hint Extern 1 (lc_Tm (t__Lam _ _)) =>
  let tx1 := fresh in
  pick_fresh tx1;
  apply (lc_t__Lam_exists tx1) : core.

#[export] Hint Extern 1 (lc_Tm (t__TLam _)) =>
  let alpha1 := fresh in
  pick_fresh alpha1;
  apply (lc_t__TLam_exists alpha1) : core.

Lemma lc_body_Ex_wrt_Ex :
forall e1 e2,
  body_Ex_wrt_Ex e1 ->
  lc_Ex e2 ->
  lc_Ex (open_Ex_wrt_Ex e1 e2).
Proof.
unfold body_Ex_wrt_Ex;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
Ex_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_Ex_wrt_Ex : lngen.

Lemma lc_body_T_wrt_T :
forall T1 T2,
  body_T_wrt_T T1 ->
  lc_T T2 ->
  lc_T (open_T_wrt_T T1 T2).
Proof.
unfold body_T_wrt_T;
default_simp;
let beta1 := fresh "x" in
pick_fresh beta1;
specialize_all beta1;
T_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_T_wrt_T : lngen.

Lemma lc_body_Sc_wrt_T :
forall Sc1 T1,
  body_Sc_wrt_T Sc1 ->
  lc_T T1 ->
  lc_Sc (open_Sc_wrt_T Sc1 T1).
Proof.
unfold body_Sc_wrt_T;
default_simp;
let beta1 := fresh "x" in
pick_fresh beta1;
specialize_all beta1;
Sc_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_Sc_wrt_T : lngen.

Lemma lc_body_Tm_wrt_T :
forall t1 T1,
  body_Tm_wrt_T t1 ->
  lc_T T1 ->
  lc_Tm (open_Tm_wrt_T t1 T1).
Proof.
unfold body_Tm_wrt_T;
default_simp;
let beta1 := fresh "x" in
pick_fresh beta1;
specialize_all beta1;
Tm_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_Tm_wrt_T : lngen.

Lemma lc_body_Tm_wrt_Tm :
forall t1 t2,
  body_Tm_wrt_Tm t1 ->
  lc_Tm t2 ->
  lc_Tm (open_Tm_wrt_Tm t1 t2).
Proof.
unfold body_Tm_wrt_Tm;
default_simp;
let tx1 := fresh "x" in
pick_fresh tx1;
specialize_all tx1;
Tm_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_Tm_wrt_Tm : lngen.

Lemma lc_body_e__Lam_1 :
forall e1,
  lc_Ex (e__Lam e1) ->
  body_Ex_wrt_Ex e1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_e__Lam_1 : lngen.

Lemma lc_body_e__Let_2 :
forall e1 e2,
  lc_Ex (e__Let e1 e2) ->
  body_Ex_wrt_Ex e2.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_e__Let_2 : lngen.

Lemma lc_body_S__Forall_1 :
forall sigma1,
  lc_Sc (S__Forall sigma1) ->
  body_Sc_wrt_T sigma1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_S__Forall_1 : lngen.

Lemma lc_body_t__Lam_2 :
forall tau1 t1,
  lc_Tm (t__Lam tau1 t1) ->
  body_Tm_wrt_Tm t1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_t__Lam_2 : lngen.

Lemma lc_body_t__TLam_1 :
forall t1,
  lc_Tm (t__TLam t1) ->
  body_Tm_wrt_T t1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_t__TLam_1 : lngen.

(* begin hide *)

Lemma lc_Ex_unique_mutual :
(forall e1 (proof2 proof3 : lc_Ex e1), proof2 = proof3).
Proof.
apply_mutual_ind lc_Ex_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_Ex_unique :
forall e1 (proof2 proof3 : lc_Ex e1), proof2 = proof3.
Proof.
pose proof lc_Ex_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_Ex_unique : lngen.

(* begin hide *)

Lemma lc_T_unique_mutual :
(forall T1 (proof2 proof3 : lc_T T1), proof2 = proof3).
Proof.
apply_mutual_ind lc_T_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_T_unique :
forall T1 (proof2 proof3 : lc_T T1), proof2 = proof3.
Proof.
pose proof lc_T_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_T_unique : lngen.

(* begin hide *)

Lemma lc_Sc_unique_mutual :
(forall Sc1 (proof2 proof3 : lc_Sc Sc1), proof2 = proof3).
Proof.
apply_mutual_ind lc_Sc_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_Sc_unique :
forall Sc1 (proof2 proof3 : lc_Sc Sc1), proof2 = proof3.
Proof.
pose proof lc_Sc_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_Sc_unique : lngen.

(* begin hide *)

Lemma lc_Tm_unique_mutual :
(forall t1 (proof2 proof3 : lc_Tm t1), proof2 = proof3).
Proof.
apply_mutual_ind lc_Tm_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_Tm_unique :
forall t1 (proof2 proof3 : lc_Tm t1), proof2 = proof3.
Proof.
pose proof lc_Tm_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_Tm_unique : lngen.

(* begin hide *)

Lemma lc_Ex_of_lc_set_Ex_mutual :
(forall e1, lc_set_Ex e1 -> lc_Ex e1).
Proof.
apply_mutual_ind lc_set_Ex_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_Ex_of_lc_set_Ex :
forall e1, lc_set_Ex e1 -> lc_Ex e1.
Proof.
pose proof lc_Ex_of_lc_set_Ex_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_Ex_of_lc_set_Ex : lngen.

(* begin hide *)

Lemma lc_T_of_lc_set_T_mutual :
(forall T1, lc_set_T T1 -> lc_T T1).
Proof.
apply_mutual_ind lc_set_T_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_T_of_lc_set_T :
forall T1, lc_set_T T1 -> lc_T T1.
Proof.
pose proof lc_T_of_lc_set_T_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_T_of_lc_set_T : lngen.

(* begin hide *)

Lemma lc_Sc_of_lc_set_Sc_mutual :
(forall Sc1, lc_set_Sc Sc1 -> lc_Sc Sc1).
Proof.
apply_mutual_ind lc_set_Sc_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_Sc_of_lc_set_Sc :
forall Sc1, lc_set_Sc Sc1 -> lc_Sc Sc1.
Proof.
pose proof lc_Sc_of_lc_set_Sc_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_Sc_of_lc_set_Sc : lngen.

(* begin hide *)

Lemma lc_Tm_of_lc_set_Tm_mutual :
(forall t1, lc_set_Tm t1 -> lc_Tm t1).
Proof.
apply_mutual_ind lc_set_Tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_Tm_of_lc_set_Tm :
forall t1, lc_set_Tm t1 -> lc_Tm t1.
Proof.
pose proof lc_Tm_of_lc_set_Tm_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_Tm_of_lc_set_Tm : lngen.

(* begin hide *)

Lemma lc_set_Ex_of_lc_Ex_size_mutual :
forall i1,
(forall e1,
  size_Ex e1 = i1 ->
  lc_Ex e1 ->
  lc_set_Ex e1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind Ex_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_Ex_of_lc_Ex];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_Ex_of_lc_Ex :
forall e1,
  lc_Ex e1 ->
  lc_set_Ex e1.
Proof.
intros e1; intros;
pose proof (lc_set_Ex_of_lc_Ex_size_mutual (size_Ex e1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_Ex_of_lc_Ex : lngen.

(* begin hide *)

Lemma lc_set_T_of_lc_T_size_mutual :
forall i1,
(forall T1,
  size_T T1 = i1 ->
  lc_T T1 ->
  lc_set_T T1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind T_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_T_of_lc_T];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_T_of_lc_T :
forall T1,
  lc_T T1 ->
  lc_set_T T1.
Proof.
intros T1; intros;
pose proof (lc_set_T_of_lc_T_size_mutual (size_T T1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_T_of_lc_T : lngen.

(* begin hide *)

Lemma lc_set_Sc_of_lc_Sc_size_mutual :
forall i1,
(forall Sc1,
  size_Sc Sc1 = i1 ->
  lc_Sc Sc1 ->
  lc_set_Sc Sc1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind Sc_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_Sc_of_lc_Sc
 | apply lc_set_T_of_lc_T];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_Sc_of_lc_Sc :
forall Sc1,
  lc_Sc Sc1 ->
  lc_set_Sc Sc1.
Proof.
intros Sc1; intros;
pose proof (lc_set_Sc_of_lc_Sc_size_mutual (size_Sc Sc1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_Sc_of_lc_Sc : lngen.

(* begin hide *)

Lemma lc_set_Tm_of_lc_Tm_size_mutual :
forall i1,
(forall t1,
  size_Tm t1 = i1 ->
  lc_Tm t1 ->
  lc_set_Tm t1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind Tm_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_T_of_lc_T
 | apply lc_set_Tm_of_lc_Tm];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_Tm_of_lc_Tm :
forall t1,
  lc_Tm t1 ->
  lc_set_Tm t1.
Proof.
intros t1; intros;
pose proof (lc_set_Tm_of_lc_Tm_size_mutual (size_Tm t1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_Tm_of_lc_Tm : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_Ex_wrt_Ex_rec_degree_Ex_wrt_Ex_mutual :
(forall e1 x1 n1,
  degree_Ex_wrt_Ex n1 e1 ->
  x1 `notin` fv_Ex e1 ->
  close_Ex_wrt_Ex_rec n1 x1 e1 = e1).
Proof.
apply_mutual_ind Ex_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_Ex_wrt_Ex_rec_degree_Ex_wrt_Ex :
forall e1 x1 n1,
  degree_Ex_wrt_Ex n1 e1 ->
  x1 `notin` fv_Ex e1 ->
  close_Ex_wrt_Ex_rec n1 x1 e1 = e1.
Proof.
pose proof close_Ex_wrt_Ex_rec_degree_Ex_wrt_Ex_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_Ex_wrt_Ex_rec_degree_Ex_wrt_Ex : lngen.
#[export] Hint Rewrite close_Ex_wrt_Ex_rec_degree_Ex_wrt_Ex using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_T_wrt_T_rec_degree_T_wrt_T_mutual :
(forall T1 beta1 n1,
  degree_T_wrt_T n1 T1 ->
  beta1 `notin` fsk_T T1 ->
  close_T_wrt_T_rec n1 beta1 T1 = T1).
Proof.
apply_mutual_ind T_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_T_wrt_T_rec_degree_T_wrt_T :
forall T1 beta1 n1,
  degree_T_wrt_T n1 T1 ->
  beta1 `notin` fsk_T T1 ->
  close_T_wrt_T_rec n1 beta1 T1 = T1.
Proof.
pose proof close_T_wrt_T_rec_degree_T_wrt_T_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_T_wrt_T_rec_degree_T_wrt_T : lngen.
#[export] Hint Rewrite close_T_wrt_T_rec_degree_T_wrt_T using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_Sc_wrt_T_rec_degree_Sc_wrt_T_mutual :
(forall Sc1 beta1 n1,
  degree_Sc_wrt_T n1 Sc1 ->
  beta1 `notin` fsk_Sc Sc1 ->
  close_Sc_wrt_T_rec n1 beta1 Sc1 = Sc1).
Proof.
apply_mutual_ind Sc_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_Sc_wrt_T_rec_degree_Sc_wrt_T :
forall Sc1 beta1 n1,
  degree_Sc_wrt_T n1 Sc1 ->
  beta1 `notin` fsk_Sc Sc1 ->
  close_Sc_wrt_T_rec n1 beta1 Sc1 = Sc1.
Proof.
pose proof close_Sc_wrt_T_rec_degree_Sc_wrt_T_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_Sc_wrt_T_rec_degree_Sc_wrt_T : lngen.
#[export] Hint Rewrite close_Sc_wrt_T_rec_degree_Sc_wrt_T using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_Tm_wrt_T_rec_degree_Tm_wrt_T_mutual :
(forall t1 beta1 n1,
  degree_Tm_wrt_T n1 t1 ->
  beta1 `notin` fsk_Tm t1 ->
  close_Tm_wrt_T_rec n1 beta1 t1 = t1).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_Tm_wrt_T_rec_degree_Tm_wrt_T :
forall t1 beta1 n1,
  degree_Tm_wrt_T n1 t1 ->
  beta1 `notin` fsk_Tm t1 ->
  close_Tm_wrt_T_rec n1 beta1 t1 = t1.
Proof.
pose proof close_Tm_wrt_T_rec_degree_Tm_wrt_T_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_Tm_wrt_T_rec_degree_Tm_wrt_T : lngen.
#[export] Hint Rewrite close_Tm_wrt_T_rec_degree_Tm_wrt_T using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_Tm_wrt_Tm_rec_degree_Tm_wrt_Tm_mutual :
(forall t1 tx1 n1,
  degree_Tm_wrt_Tm n1 t1 ->
  tx1 `notin` ftv_Tm t1 ->
  close_Tm_wrt_Tm_rec n1 tx1 t1 = t1).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_Tm_wrt_Tm_rec_degree_Tm_wrt_Tm :
forall t1 tx1 n1,
  degree_Tm_wrt_Tm n1 t1 ->
  tx1 `notin` ftv_Tm t1 ->
  close_Tm_wrt_Tm_rec n1 tx1 t1 = t1.
Proof.
pose proof close_Tm_wrt_Tm_rec_degree_Tm_wrt_Tm_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_Tm_wrt_Tm_rec_degree_Tm_wrt_Tm : lngen.
#[export] Hint Rewrite close_Tm_wrt_Tm_rec_degree_Tm_wrt_Tm using solve [auto] : lngen.

(* end hide *)

Lemma close_Ex_wrt_Ex_lc_Ex :
forall e1 x1,
  lc_Ex e1 ->
  x1 `notin` fv_Ex e1 ->
  close_Ex_wrt_Ex x1 e1 = e1.
Proof.
unfold close_Ex_wrt_Ex; default_simp.
Qed.

#[export] Hint Resolve close_Ex_wrt_Ex_lc_Ex : lngen.
#[export] Hint Rewrite close_Ex_wrt_Ex_lc_Ex using solve [auto] : lngen.

Lemma close_T_wrt_T_lc_T :
forall T1 beta1,
  lc_T T1 ->
  beta1 `notin` fsk_T T1 ->
  close_T_wrt_T beta1 T1 = T1.
Proof.
unfold close_T_wrt_T; default_simp.
Qed.

#[export] Hint Resolve close_T_wrt_T_lc_T : lngen.
#[export] Hint Rewrite close_T_wrt_T_lc_T using solve [auto] : lngen.

Lemma close_Sc_wrt_T_lc_Sc :
forall Sc1 beta1,
  lc_Sc Sc1 ->
  beta1 `notin` fsk_Sc Sc1 ->
  close_Sc_wrt_T beta1 Sc1 = Sc1.
Proof.
unfold close_Sc_wrt_T; default_simp.
Qed.

#[export] Hint Resolve close_Sc_wrt_T_lc_Sc : lngen.
#[export] Hint Rewrite close_Sc_wrt_T_lc_Sc using solve [auto] : lngen.

Lemma close_Tm_wrt_T_lc_Tm :
forall t1 beta1,
  lc_Tm t1 ->
  beta1 `notin` fsk_Tm t1 ->
  close_Tm_wrt_T beta1 t1 = t1.
Proof.
unfold close_Tm_wrt_T; default_simp.
Qed.

#[export] Hint Resolve close_Tm_wrt_T_lc_Tm : lngen.
#[export] Hint Rewrite close_Tm_wrt_T_lc_Tm using solve [auto] : lngen.

Lemma close_Tm_wrt_Tm_lc_Tm :
forall t1 tx1,
  lc_Tm t1 ->
  tx1 `notin` ftv_Tm t1 ->
  close_Tm_wrt_Tm tx1 t1 = t1.
Proof.
unfold close_Tm_wrt_Tm; default_simp.
Qed.

#[export] Hint Resolve close_Tm_wrt_Tm_lc_Tm : lngen.
#[export] Hint Rewrite close_Tm_wrt_Tm_lc_Tm using solve [auto] : lngen.

(* begin hide *)

Lemma open_Ex_wrt_Ex_rec_degree_Ex_wrt_Ex_mutual :
(forall e2 e1 n1,
  degree_Ex_wrt_Ex n1 e2 ->
  open_Ex_wrt_Ex_rec n1 e1 e2 = e2).
Proof.
apply_mutual_ind Ex_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_Ex_wrt_Ex_rec_degree_Ex_wrt_Ex :
forall e2 e1 n1,
  degree_Ex_wrt_Ex n1 e2 ->
  open_Ex_wrt_Ex_rec n1 e1 e2 = e2.
Proof.
pose proof open_Ex_wrt_Ex_rec_degree_Ex_wrt_Ex_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_Ex_wrt_Ex_rec_degree_Ex_wrt_Ex : lngen.
#[export] Hint Rewrite open_Ex_wrt_Ex_rec_degree_Ex_wrt_Ex using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_T_wrt_T_rec_degree_T_wrt_T_mutual :
(forall T2 T1 n1,
  degree_T_wrt_T n1 T2 ->
  open_T_wrt_T_rec n1 T1 T2 = T2).
Proof.
apply_mutual_ind T_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_T_wrt_T_rec_degree_T_wrt_T :
forall T2 T1 n1,
  degree_T_wrt_T n1 T2 ->
  open_T_wrt_T_rec n1 T1 T2 = T2.
Proof.
pose proof open_T_wrt_T_rec_degree_T_wrt_T_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_T_wrt_T_rec_degree_T_wrt_T : lngen.
#[export] Hint Rewrite open_T_wrt_T_rec_degree_T_wrt_T using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_Sc_wrt_T_rec_degree_Sc_wrt_T_mutual :
(forall Sc1 T1 n1,
  degree_Sc_wrt_T n1 Sc1 ->
  open_Sc_wrt_T_rec n1 T1 Sc1 = Sc1).
Proof.
apply_mutual_ind Sc_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_Sc_wrt_T_rec_degree_Sc_wrt_T :
forall Sc1 T1 n1,
  degree_Sc_wrt_T n1 Sc1 ->
  open_Sc_wrt_T_rec n1 T1 Sc1 = Sc1.
Proof.
pose proof open_Sc_wrt_T_rec_degree_Sc_wrt_T_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_Sc_wrt_T_rec_degree_Sc_wrt_T : lngen.
#[export] Hint Rewrite open_Sc_wrt_T_rec_degree_Sc_wrt_T using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_Tm_wrt_T_rec_degree_Tm_wrt_T_mutual :
(forall t1 T1 n1,
  degree_Tm_wrt_T n1 t1 ->
  open_Tm_wrt_T_rec n1 T1 t1 = t1).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_Tm_wrt_T_rec_degree_Tm_wrt_T :
forall t1 T1 n1,
  degree_Tm_wrt_T n1 t1 ->
  open_Tm_wrt_T_rec n1 T1 t1 = t1.
Proof.
pose proof open_Tm_wrt_T_rec_degree_Tm_wrt_T_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_Tm_wrt_T_rec_degree_Tm_wrt_T : lngen.
#[export] Hint Rewrite open_Tm_wrt_T_rec_degree_Tm_wrt_T using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_Tm_wrt_Tm_rec_degree_Tm_wrt_Tm_mutual :
(forall t2 t1 n1,
  degree_Tm_wrt_Tm n1 t2 ->
  open_Tm_wrt_Tm_rec n1 t1 t2 = t2).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_Tm_wrt_Tm_rec_degree_Tm_wrt_Tm :
forall t2 t1 n1,
  degree_Tm_wrt_Tm n1 t2 ->
  open_Tm_wrt_Tm_rec n1 t1 t2 = t2.
Proof.
pose proof open_Tm_wrt_Tm_rec_degree_Tm_wrt_Tm_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_Tm_wrt_Tm_rec_degree_Tm_wrt_Tm : lngen.
#[export] Hint Rewrite open_Tm_wrt_Tm_rec_degree_Tm_wrt_Tm using solve [auto] : lngen.

(* end hide *)

Lemma open_Ex_wrt_Ex_lc_Ex :
forall e2 e1,
  lc_Ex e2 ->
  open_Ex_wrt_Ex e2 e1 = e2.
Proof.
unfold open_Ex_wrt_Ex; default_simp.
Qed.

#[export] Hint Resolve open_Ex_wrt_Ex_lc_Ex : lngen.
#[export] Hint Rewrite open_Ex_wrt_Ex_lc_Ex using solve [auto] : lngen.

Lemma open_T_wrt_T_lc_T :
forall T2 T1,
  lc_T T2 ->
  open_T_wrt_T T2 T1 = T2.
Proof.
unfold open_T_wrt_T; default_simp.
Qed.

#[export] Hint Resolve open_T_wrt_T_lc_T : lngen.
#[export] Hint Rewrite open_T_wrt_T_lc_T using solve [auto] : lngen.

Lemma open_Sc_wrt_T_lc_Sc :
forall Sc1 T1,
  lc_Sc Sc1 ->
  open_Sc_wrt_T Sc1 T1 = Sc1.
Proof.
unfold open_Sc_wrt_T; default_simp.
Qed.

#[export] Hint Resolve open_Sc_wrt_T_lc_Sc : lngen.
#[export] Hint Rewrite open_Sc_wrt_T_lc_Sc using solve [auto] : lngen.

Lemma open_Tm_wrt_T_lc_Tm :
forall t1 T1,
  lc_Tm t1 ->
  open_Tm_wrt_T t1 T1 = t1.
Proof.
unfold open_Tm_wrt_T; default_simp.
Qed.

#[export] Hint Resolve open_Tm_wrt_T_lc_Tm : lngen.
#[export] Hint Rewrite open_Tm_wrt_T_lc_Tm using solve [auto] : lngen.

Lemma open_Tm_wrt_Tm_lc_Tm :
forall t2 t1,
  lc_Tm t2 ->
  open_Tm_wrt_Tm t2 t1 = t2.
Proof.
unfold open_Tm_wrt_Tm; default_simp.
Qed.

#[export] Hint Resolve open_Tm_wrt_Tm_lc_Tm : lngen.
#[export] Hint Rewrite open_Tm_wrt_Tm_lc_Tm using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma fv_Ex_close_Ex_wrt_Ex_rec_mutual :
(forall e1 x1 n1,
  fv_Ex (close_Ex_wrt_Ex_rec n1 x1 e1) [=] remove x1 (fv_Ex e1)).
Proof.
apply_mutual_ind Ex_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_Ex_close_Ex_wrt_Ex_rec :
forall e1 x1 n1,
  fv_Ex (close_Ex_wrt_Ex_rec n1 x1 e1) [=] remove x1 (fv_Ex e1).
Proof.
pose proof fv_Ex_close_Ex_wrt_Ex_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_Ex_close_Ex_wrt_Ex_rec : lngen.
#[export] Hint Rewrite fv_Ex_close_Ex_wrt_Ex_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fsk_T_close_T_wrt_T_rec_mutual :
(forall T1 beta1 n1,
  fsk_T (close_T_wrt_T_rec n1 beta1 T1) [=] remove beta1 (fsk_T T1)).
Proof.
apply_mutual_ind T_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fsk_T_close_T_wrt_T_rec :
forall T1 beta1 n1,
  fsk_T (close_T_wrt_T_rec n1 beta1 T1) [=] remove beta1 (fsk_T T1).
Proof.
pose proof fsk_T_close_T_wrt_T_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fsk_T_close_T_wrt_T_rec : lngen.
#[export] Hint Rewrite fsk_T_close_T_wrt_T_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fsk_Sc_close_Sc_wrt_T_rec_mutual :
(forall Sc1 beta1 n1,
  fsk_Sc (close_Sc_wrt_T_rec n1 beta1 Sc1) [=] remove beta1 (fsk_Sc Sc1)).
Proof.
apply_mutual_ind Sc_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fsk_Sc_close_Sc_wrt_T_rec :
forall Sc1 beta1 n1,
  fsk_Sc (close_Sc_wrt_T_rec n1 beta1 Sc1) [=] remove beta1 (fsk_Sc Sc1).
Proof.
pose proof fsk_Sc_close_Sc_wrt_T_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fsk_Sc_close_Sc_wrt_T_rec : lngen.
#[export] Hint Rewrite fsk_Sc_close_Sc_wrt_T_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fsk_Tm_close_Tm_wrt_T_rec_mutual :
(forall t1 beta1 n1,
  fsk_Tm (close_Tm_wrt_T_rec n1 beta1 t1) [=] remove beta1 (fsk_Tm t1)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fsk_Tm_close_Tm_wrt_T_rec :
forall t1 beta1 n1,
  fsk_Tm (close_Tm_wrt_T_rec n1 beta1 t1) [=] remove beta1 (fsk_Tm t1).
Proof.
pose proof fsk_Tm_close_Tm_wrt_T_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fsk_Tm_close_Tm_wrt_T_rec : lngen.
#[export] Hint Rewrite fsk_Tm_close_Tm_wrt_T_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fsk_Tm_close_Tm_wrt_Tm_rec_mutual :
(forall t1 tx1 n1,
  fsk_Tm (close_Tm_wrt_Tm_rec n1 tx1 t1) [=] fsk_Tm t1).
Proof.
apply_mutual_ind Tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fsk_Tm_close_Tm_wrt_Tm_rec :
forall t1 tx1 n1,
  fsk_Tm (close_Tm_wrt_Tm_rec n1 tx1 t1) [=] fsk_Tm t1.
Proof.
pose proof fsk_Tm_close_Tm_wrt_Tm_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fsk_Tm_close_Tm_wrt_Tm_rec : lngen.
#[export] Hint Rewrite fsk_Tm_close_Tm_wrt_Tm_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_Tm_close_Tm_wrt_T_rec_mutual :
(forall t1 beta1 n1,
  ftv_Tm (close_Tm_wrt_T_rec n1 beta1 t1) [=] ftv_Tm t1).
Proof.
apply_mutual_ind Tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_Tm_close_Tm_wrt_T_rec :
forall t1 beta1 n1,
  ftv_Tm (close_Tm_wrt_T_rec n1 beta1 t1) [=] ftv_Tm t1.
Proof.
pose proof ftv_Tm_close_Tm_wrt_T_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_Tm_close_Tm_wrt_T_rec : lngen.
#[export] Hint Rewrite ftv_Tm_close_Tm_wrt_T_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_Tm_close_Tm_wrt_Tm_rec_mutual :
(forall t1 tx1 n1,
  ftv_Tm (close_Tm_wrt_Tm_rec n1 tx1 t1) [=] remove tx1 (ftv_Tm t1)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_Tm_close_Tm_wrt_Tm_rec :
forall t1 tx1 n1,
  ftv_Tm (close_Tm_wrt_Tm_rec n1 tx1 t1) [=] remove tx1 (ftv_Tm t1).
Proof.
pose proof ftv_Tm_close_Tm_wrt_Tm_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_Tm_close_Tm_wrt_Tm_rec : lngen.
#[export] Hint Rewrite ftv_Tm_close_Tm_wrt_Tm_rec using solve [auto] : lngen.

(* end hide *)

Lemma fv_Ex_close_Ex_wrt_Ex :
forall e1 x1,
  fv_Ex (close_Ex_wrt_Ex x1 e1) [=] remove x1 (fv_Ex e1).
Proof.
unfold close_Ex_wrt_Ex; default_simp.
Qed.

#[export] Hint Resolve fv_Ex_close_Ex_wrt_Ex : lngen.
#[export] Hint Rewrite fv_Ex_close_Ex_wrt_Ex using solve [auto] : lngen.

Lemma fsk_T_close_T_wrt_T :
forall T1 beta1,
  fsk_T (close_T_wrt_T beta1 T1) [=] remove beta1 (fsk_T T1).
Proof.
unfold close_T_wrt_T; default_simp.
Qed.

#[export] Hint Resolve fsk_T_close_T_wrt_T : lngen.
#[export] Hint Rewrite fsk_T_close_T_wrt_T using solve [auto] : lngen.

Lemma fsk_Sc_close_Sc_wrt_T :
forall Sc1 beta1,
  fsk_Sc (close_Sc_wrt_T beta1 Sc1) [=] remove beta1 (fsk_Sc Sc1).
Proof.
unfold close_Sc_wrt_T; default_simp.
Qed.

#[export] Hint Resolve fsk_Sc_close_Sc_wrt_T : lngen.
#[export] Hint Rewrite fsk_Sc_close_Sc_wrt_T using solve [auto] : lngen.

Lemma fsk_Tm_close_Tm_wrt_T :
forall t1 beta1,
  fsk_Tm (close_Tm_wrt_T beta1 t1) [=] remove beta1 (fsk_Tm t1).
Proof.
unfold close_Tm_wrt_T; default_simp.
Qed.

#[export] Hint Resolve fsk_Tm_close_Tm_wrt_T : lngen.
#[export] Hint Rewrite fsk_Tm_close_Tm_wrt_T using solve [auto] : lngen.

Lemma fsk_Tm_close_Tm_wrt_Tm :
forall t1 tx1,
  fsk_Tm (close_Tm_wrt_Tm tx1 t1) [=] fsk_Tm t1.
Proof.
unfold close_Tm_wrt_Tm; default_simp.
Qed.

#[export] Hint Resolve fsk_Tm_close_Tm_wrt_Tm : lngen.
#[export] Hint Rewrite fsk_Tm_close_Tm_wrt_Tm using solve [auto] : lngen.

Lemma ftv_Tm_close_Tm_wrt_T :
forall t1 beta1,
  ftv_Tm (close_Tm_wrt_T beta1 t1) [=] ftv_Tm t1.
Proof.
unfold close_Tm_wrt_T; default_simp.
Qed.

#[export] Hint Resolve ftv_Tm_close_Tm_wrt_T : lngen.
#[export] Hint Rewrite ftv_Tm_close_Tm_wrt_T using solve [auto] : lngen.

Lemma ftv_Tm_close_Tm_wrt_Tm :
forall t1 tx1,
  ftv_Tm (close_Tm_wrt_Tm tx1 t1) [=] remove tx1 (ftv_Tm t1).
Proof.
unfold close_Tm_wrt_Tm; default_simp.
Qed.

#[export] Hint Resolve ftv_Tm_close_Tm_wrt_Tm : lngen.
#[export] Hint Rewrite ftv_Tm_close_Tm_wrt_Tm using solve [auto] : lngen.

(* begin hide *)

Lemma fv_Ex_open_Ex_wrt_Ex_rec_lower_mutual :
(forall e1 e2 n1,
  fv_Ex e1 [<=] fv_Ex (open_Ex_wrt_Ex_rec n1 e2 e1)).
Proof.
apply_mutual_ind Ex_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_Ex_open_Ex_wrt_Ex_rec_lower :
forall e1 e2 n1,
  fv_Ex e1 [<=] fv_Ex (open_Ex_wrt_Ex_rec n1 e2 e1).
Proof.
pose proof fv_Ex_open_Ex_wrt_Ex_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_Ex_open_Ex_wrt_Ex_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fsk_T_open_T_wrt_T_rec_lower_mutual :
(forall T1 T2 n1,
  fsk_T T1 [<=] fsk_T (open_T_wrt_T_rec n1 T2 T1)).
Proof.
apply_mutual_ind T_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fsk_T_open_T_wrt_T_rec_lower :
forall T1 T2 n1,
  fsk_T T1 [<=] fsk_T (open_T_wrt_T_rec n1 T2 T1).
Proof.
pose proof fsk_T_open_T_wrt_T_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fsk_T_open_T_wrt_T_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fsk_Sc_open_Sc_wrt_T_rec_lower_mutual :
(forall Sc1 T1 n1,
  fsk_Sc Sc1 [<=] fsk_Sc (open_Sc_wrt_T_rec n1 T1 Sc1)).
Proof.
apply_mutual_ind Sc_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fsk_Sc_open_Sc_wrt_T_rec_lower :
forall Sc1 T1 n1,
  fsk_Sc Sc1 [<=] fsk_Sc (open_Sc_wrt_T_rec n1 T1 Sc1).
Proof.
pose proof fsk_Sc_open_Sc_wrt_T_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fsk_Sc_open_Sc_wrt_T_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fsk_Tm_open_Tm_wrt_T_rec_lower_mutual :
(forall t1 T1 n1,
  fsk_Tm t1 [<=] fsk_Tm (open_Tm_wrt_T_rec n1 T1 t1)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fsk_Tm_open_Tm_wrt_T_rec_lower :
forall t1 T1 n1,
  fsk_Tm t1 [<=] fsk_Tm (open_Tm_wrt_T_rec n1 T1 t1).
Proof.
pose proof fsk_Tm_open_Tm_wrt_T_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fsk_Tm_open_Tm_wrt_T_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fsk_Tm_open_Tm_wrt_Tm_rec_lower_mutual :
(forall t1 t2 n1,
  fsk_Tm t1 [<=] fsk_Tm (open_Tm_wrt_Tm_rec n1 t2 t1)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fsk_Tm_open_Tm_wrt_Tm_rec_lower :
forall t1 t2 n1,
  fsk_Tm t1 [<=] fsk_Tm (open_Tm_wrt_Tm_rec n1 t2 t1).
Proof.
pose proof fsk_Tm_open_Tm_wrt_Tm_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fsk_Tm_open_Tm_wrt_Tm_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_Tm_open_Tm_wrt_T_rec_lower_mutual :
(forall t1 T1 n1,
  ftv_Tm t1 [<=] ftv_Tm (open_Tm_wrt_T_rec n1 T1 t1)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_Tm_open_Tm_wrt_T_rec_lower :
forall t1 T1 n1,
  ftv_Tm t1 [<=] ftv_Tm (open_Tm_wrt_T_rec n1 T1 t1).
Proof.
pose proof ftv_Tm_open_Tm_wrt_T_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_Tm_open_Tm_wrt_T_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_Tm_open_Tm_wrt_Tm_rec_lower_mutual :
(forall t1 t2 n1,
  ftv_Tm t1 [<=] ftv_Tm (open_Tm_wrt_Tm_rec n1 t2 t1)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_Tm_open_Tm_wrt_Tm_rec_lower :
forall t1 t2 n1,
  ftv_Tm t1 [<=] ftv_Tm (open_Tm_wrt_Tm_rec n1 t2 t1).
Proof.
pose proof ftv_Tm_open_Tm_wrt_Tm_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_Tm_open_Tm_wrt_Tm_rec_lower : lngen.

(* end hide *)

Lemma fv_Ex_open_Ex_wrt_Ex_lower :
forall e1 e2,
  fv_Ex e1 [<=] fv_Ex (open_Ex_wrt_Ex e1 e2).
Proof.
unfold open_Ex_wrt_Ex; default_simp.
Qed.

#[export] Hint Resolve fv_Ex_open_Ex_wrt_Ex_lower : lngen.

Lemma fsk_T_open_T_wrt_T_lower :
forall T1 T2,
  fsk_T T1 [<=] fsk_T (open_T_wrt_T T1 T2).
Proof.
unfold open_T_wrt_T; default_simp.
Qed.

#[export] Hint Resolve fsk_T_open_T_wrt_T_lower : lngen.

Lemma fsk_Sc_open_Sc_wrt_T_lower :
forall Sc1 T1,
  fsk_Sc Sc1 [<=] fsk_Sc (open_Sc_wrt_T Sc1 T1).
Proof.
unfold open_Sc_wrt_T; default_simp.
Qed.

#[export] Hint Resolve fsk_Sc_open_Sc_wrt_T_lower : lngen.

Lemma fsk_Tm_open_Tm_wrt_T_lower :
forall t1 T1,
  fsk_Tm t1 [<=] fsk_Tm (open_Tm_wrt_T t1 T1).
Proof.
unfold open_Tm_wrt_T; default_simp.
Qed.

#[export] Hint Resolve fsk_Tm_open_Tm_wrt_T_lower : lngen.

Lemma fsk_Tm_open_Tm_wrt_Tm_lower :
forall t1 t2,
  fsk_Tm t1 [<=] fsk_Tm (open_Tm_wrt_Tm t1 t2).
Proof.
unfold open_Tm_wrt_Tm; default_simp.
Qed.

#[export] Hint Resolve fsk_Tm_open_Tm_wrt_Tm_lower : lngen.

Lemma ftv_Tm_open_Tm_wrt_T_lower :
forall t1 T1,
  ftv_Tm t1 [<=] ftv_Tm (open_Tm_wrt_T t1 T1).
Proof.
unfold open_Tm_wrt_T; default_simp.
Qed.

#[export] Hint Resolve ftv_Tm_open_Tm_wrt_T_lower : lngen.

Lemma ftv_Tm_open_Tm_wrt_Tm_lower :
forall t1 t2,
  ftv_Tm t1 [<=] ftv_Tm (open_Tm_wrt_Tm t1 t2).
Proof.
unfold open_Tm_wrt_Tm; default_simp.
Qed.

#[export] Hint Resolve ftv_Tm_open_Tm_wrt_Tm_lower : lngen.

(* begin hide *)

Lemma fv_Ex_open_Ex_wrt_Ex_rec_upper_mutual :
(forall e1 e2 n1,
  fv_Ex (open_Ex_wrt_Ex_rec n1 e2 e1) [<=] fv_Ex e2 `union` fv_Ex e1).
Proof.
apply_mutual_ind Ex_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_Ex_open_Ex_wrt_Ex_rec_upper :
forall e1 e2 n1,
  fv_Ex (open_Ex_wrt_Ex_rec n1 e2 e1) [<=] fv_Ex e2 `union` fv_Ex e1.
Proof.
pose proof fv_Ex_open_Ex_wrt_Ex_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_Ex_open_Ex_wrt_Ex_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fsk_T_open_T_wrt_T_rec_upper_mutual :
(forall T1 T2 n1,
  fsk_T (open_T_wrt_T_rec n1 T2 T1) [<=] fsk_T T2 `union` fsk_T T1).
Proof.
apply_mutual_ind T_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fsk_T_open_T_wrt_T_rec_upper :
forall T1 T2 n1,
  fsk_T (open_T_wrt_T_rec n1 T2 T1) [<=] fsk_T T2 `union` fsk_T T1.
Proof.
pose proof fsk_T_open_T_wrt_T_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fsk_T_open_T_wrt_T_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fsk_Sc_open_Sc_wrt_T_rec_upper_mutual :
(forall Sc1 T1 n1,
  fsk_Sc (open_Sc_wrt_T_rec n1 T1 Sc1) [<=] fsk_T T1 `union` fsk_Sc Sc1).
Proof.
apply_mutual_ind Sc_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fsk_Sc_open_Sc_wrt_T_rec_upper :
forall Sc1 T1 n1,
  fsk_Sc (open_Sc_wrt_T_rec n1 T1 Sc1) [<=] fsk_T T1 `union` fsk_Sc Sc1.
Proof.
pose proof fsk_Sc_open_Sc_wrt_T_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fsk_Sc_open_Sc_wrt_T_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fsk_Tm_open_Tm_wrt_T_rec_upper_mutual :
(forall t1 T1 n1,
  fsk_Tm (open_Tm_wrt_T_rec n1 T1 t1) [<=] fsk_T T1 `union` fsk_Tm t1).
Proof.
apply_mutual_ind Tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fsk_Tm_open_Tm_wrt_T_rec_upper :
forall t1 T1 n1,
  fsk_Tm (open_Tm_wrt_T_rec n1 T1 t1) [<=] fsk_T T1 `union` fsk_Tm t1.
Proof.
pose proof fsk_Tm_open_Tm_wrt_T_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fsk_Tm_open_Tm_wrt_T_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fsk_Tm_open_Tm_wrt_Tm_rec_upper_mutual :
(forall t1 t2 n1,
  fsk_Tm (open_Tm_wrt_Tm_rec n1 t2 t1) [<=] fsk_Tm t2 `union` fsk_Tm t1).
Proof.
apply_mutual_ind Tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fsk_Tm_open_Tm_wrt_Tm_rec_upper :
forall t1 t2 n1,
  fsk_Tm (open_Tm_wrt_Tm_rec n1 t2 t1) [<=] fsk_Tm t2 `union` fsk_Tm t1.
Proof.
pose proof fsk_Tm_open_Tm_wrt_Tm_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fsk_Tm_open_Tm_wrt_Tm_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_Tm_open_Tm_wrt_T_rec_upper_mutual :
(forall t1 T1 n1,
  ftv_Tm (open_Tm_wrt_T_rec n1 T1 t1) [<=] ftv_Tm t1).
Proof.
apply_mutual_ind Tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_Tm_open_Tm_wrt_T_rec_upper :
forall t1 T1 n1,
  ftv_Tm (open_Tm_wrt_T_rec n1 T1 t1) [<=] ftv_Tm t1.
Proof.
pose proof ftv_Tm_open_Tm_wrt_T_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_Tm_open_Tm_wrt_T_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_Tm_open_Tm_wrt_Tm_rec_upper_mutual :
(forall t1 t2 n1,
  ftv_Tm (open_Tm_wrt_Tm_rec n1 t2 t1) [<=] ftv_Tm t2 `union` ftv_Tm t1).
Proof.
apply_mutual_ind Tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_Tm_open_Tm_wrt_Tm_rec_upper :
forall t1 t2 n1,
  ftv_Tm (open_Tm_wrt_Tm_rec n1 t2 t1) [<=] ftv_Tm t2 `union` ftv_Tm t1.
Proof.
pose proof ftv_Tm_open_Tm_wrt_Tm_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_Tm_open_Tm_wrt_Tm_rec_upper : lngen.

(* end hide *)

Lemma fv_Ex_open_Ex_wrt_Ex_upper :
forall e1 e2,
  fv_Ex (open_Ex_wrt_Ex e1 e2) [<=] fv_Ex e2 `union` fv_Ex e1.
Proof.
unfold open_Ex_wrt_Ex; default_simp.
Qed.

#[export] Hint Resolve fv_Ex_open_Ex_wrt_Ex_upper : lngen.

Lemma fsk_T_open_T_wrt_T_upper :
forall T1 T2,
  fsk_T (open_T_wrt_T T1 T2) [<=] fsk_T T2 `union` fsk_T T1.
Proof.
unfold open_T_wrt_T; default_simp.
Qed.

#[export] Hint Resolve fsk_T_open_T_wrt_T_upper : lngen.

Lemma fsk_Sc_open_Sc_wrt_T_upper :
forall Sc1 T1,
  fsk_Sc (open_Sc_wrt_T Sc1 T1) [<=] fsk_T T1 `union` fsk_Sc Sc1.
Proof.
unfold open_Sc_wrt_T; default_simp.
Qed.

#[export] Hint Resolve fsk_Sc_open_Sc_wrt_T_upper : lngen.

Lemma fsk_Tm_open_Tm_wrt_T_upper :
forall t1 T1,
  fsk_Tm (open_Tm_wrt_T t1 T1) [<=] fsk_T T1 `union` fsk_Tm t1.
Proof.
unfold open_Tm_wrt_T; default_simp.
Qed.

#[export] Hint Resolve fsk_Tm_open_Tm_wrt_T_upper : lngen.

Lemma fsk_Tm_open_Tm_wrt_Tm_upper :
forall t1 t2,
  fsk_Tm (open_Tm_wrt_Tm t1 t2) [<=] fsk_Tm t2 `union` fsk_Tm t1.
Proof.
unfold open_Tm_wrt_Tm; default_simp.
Qed.

#[export] Hint Resolve fsk_Tm_open_Tm_wrt_Tm_upper : lngen.

Lemma ftv_Tm_open_Tm_wrt_T_upper :
forall t1 T1,
  ftv_Tm (open_Tm_wrt_T t1 T1) [<=] ftv_Tm t1.
Proof.
unfold open_Tm_wrt_T; default_simp.
Qed.

#[export] Hint Resolve ftv_Tm_open_Tm_wrt_T_upper : lngen.

Lemma ftv_Tm_open_Tm_wrt_Tm_upper :
forall t1 t2,
  ftv_Tm (open_Tm_wrt_Tm t1 t2) [<=] ftv_Tm t2 `union` ftv_Tm t1.
Proof.
unfold open_Tm_wrt_Tm; default_simp.
Qed.

#[export] Hint Resolve ftv_Tm_open_Tm_wrt_Tm_upper : lngen.

(* begin hide *)

Lemma fv_Ex_subst_var_Ex_fresh_mutual :
(forall e1 e2 x1,
  x1 `notin` fv_Ex e1 ->
  fv_Ex (subst_var_Ex e2 x1 e1) [=] fv_Ex e1).
Proof.
apply_mutual_ind Ex_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_Ex_subst_var_Ex_fresh :
forall e1 e2 x1,
  x1 `notin` fv_Ex e1 ->
  fv_Ex (subst_var_Ex e2 x1 e1) [=] fv_Ex e1.
Proof.
pose proof fv_Ex_subst_var_Ex_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_Ex_subst_var_Ex_fresh : lngen.
#[export] Hint Rewrite fv_Ex_subst_var_Ex_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fsk_T_subst_skvar_T_fresh_mutual :
(forall T1 T2 beta1,
  beta1 `notin` fsk_T T1 ->
  fsk_T (subst_skvar_T T2 beta1 T1) [=] fsk_T T1).
Proof.
apply_mutual_ind T_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fsk_T_subst_skvar_T_fresh :
forall T1 T2 beta1,
  beta1 `notin` fsk_T T1 ->
  fsk_T (subst_skvar_T T2 beta1 T1) [=] fsk_T T1.
Proof.
pose proof fsk_T_subst_skvar_T_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fsk_T_subst_skvar_T_fresh : lngen.
#[export] Hint Rewrite fsk_T_subst_skvar_T_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fsk_Sc_subst_skvar_Sc_fresh_mutual :
(forall Sc1 T1 beta1,
  beta1 `notin` fsk_Sc Sc1 ->
  fsk_Sc (subst_skvar_Sc T1 beta1 Sc1) [=] fsk_Sc Sc1).
Proof.
apply_mutual_ind Sc_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fsk_Sc_subst_skvar_Sc_fresh :
forall Sc1 T1 beta1,
  beta1 `notin` fsk_Sc Sc1 ->
  fsk_Sc (subst_skvar_Sc T1 beta1 Sc1) [=] fsk_Sc Sc1.
Proof.
pose proof fsk_Sc_subst_skvar_Sc_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fsk_Sc_subst_skvar_Sc_fresh : lngen.
#[export] Hint Rewrite fsk_Sc_subst_skvar_Sc_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fsk_Tm_subst_skvar_Tm_fresh_mutual :
(forall t1 T1 beta1,
  beta1 `notin` fsk_Tm t1 ->
  fsk_Tm (subst_skvar_Tm T1 beta1 t1) [=] fsk_Tm t1).
Proof.
apply_mutual_ind Tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fsk_Tm_subst_skvar_Tm_fresh :
forall t1 T1 beta1,
  beta1 `notin` fsk_Tm t1 ->
  fsk_Tm (subst_skvar_Tm T1 beta1 t1) [=] fsk_Tm t1.
Proof.
pose proof fsk_Tm_subst_skvar_Tm_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fsk_Tm_subst_skvar_Tm_fresh : lngen.
#[export] Hint Rewrite fsk_Tm_subst_skvar_Tm_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fsk_Tm_subst_tvar_Tm_fresh_mutual :
(forall t1 T1 beta1,
  ftv_Tm (subst_skvar_Tm T1 beta1 t1) [=] ftv_Tm t1).
Proof.
apply_mutual_ind Tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fsk_Tm_subst_tvar_Tm_fresh :
forall t1 T1 beta1,
  ftv_Tm (subst_skvar_Tm T1 beta1 t1) [=] ftv_Tm t1.
Proof.
pose proof fsk_Tm_subst_tvar_Tm_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fsk_Tm_subst_tvar_Tm_fresh : lngen.
#[export] Hint Rewrite fsk_Tm_subst_tvar_Tm_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftv_Tm_subst_tvar_Tm_fresh_mutual :
(forall t1 t2 tx1,
  tx1 `notin` ftv_Tm t1 ->
  ftv_Tm (subst_tvar_Tm t2 tx1 t1) [=] ftv_Tm t1).
Proof.
apply_mutual_ind Tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_Tm_subst_tvar_Tm_fresh :
forall t1 t2 tx1,
  tx1 `notin` ftv_Tm t1 ->
  ftv_Tm (subst_tvar_Tm t2 tx1 t1) [=] ftv_Tm t1.
Proof.
pose proof ftv_Tm_subst_tvar_Tm_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_Tm_subst_tvar_Tm_fresh : lngen.
#[export] Hint Rewrite ftv_Tm_subst_tvar_Tm_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_Ex_subst_var_Ex_lower_mutual :
(forall e1 e2 x1,
  remove x1 (fv_Ex e1) [<=] fv_Ex (subst_var_Ex e2 x1 e1)).
Proof.
apply_mutual_ind Ex_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_Ex_subst_var_Ex_lower :
forall e1 e2 x1,
  remove x1 (fv_Ex e1) [<=] fv_Ex (subst_var_Ex e2 x1 e1).
Proof.
pose proof fv_Ex_subst_var_Ex_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_Ex_subst_var_Ex_lower : lngen.

(* begin hide *)

Lemma fsk_T_subst_skvar_T_lower_mutual :
(forall T1 T2 beta1,
  remove beta1 (fsk_T T1) [<=] fsk_T (subst_skvar_T T2 beta1 T1)).
Proof.
apply_mutual_ind T_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fsk_T_subst_skvar_T_lower :
forall T1 T2 beta1,
  remove beta1 (fsk_T T1) [<=] fsk_T (subst_skvar_T T2 beta1 T1).
Proof.
pose proof fsk_T_subst_skvar_T_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fsk_T_subst_skvar_T_lower : lngen.

(* begin hide *)

Lemma fsk_Sc_subst_skvar_Sc_lower_mutual :
(forall Sc1 T1 beta1,
  remove beta1 (fsk_Sc Sc1) [<=] fsk_Sc (subst_skvar_Sc T1 beta1 Sc1)).
Proof.
apply_mutual_ind Sc_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fsk_Sc_subst_skvar_Sc_lower :
forall Sc1 T1 beta1,
  remove beta1 (fsk_Sc Sc1) [<=] fsk_Sc (subst_skvar_Sc T1 beta1 Sc1).
Proof.
pose proof fsk_Sc_subst_skvar_Sc_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fsk_Sc_subst_skvar_Sc_lower : lngen.

(* begin hide *)

Lemma fsk_Tm_subst_skvar_Tm_lower_mutual :
(forall t1 T1 beta1,
  remove beta1 (fsk_Tm t1) [<=] fsk_Tm (subst_skvar_Tm T1 beta1 t1)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fsk_Tm_subst_skvar_Tm_lower :
forall t1 T1 beta1,
  remove beta1 (fsk_Tm t1) [<=] fsk_Tm (subst_skvar_Tm T1 beta1 t1).
Proof.
pose proof fsk_Tm_subst_skvar_Tm_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fsk_Tm_subst_skvar_Tm_lower : lngen.

(* begin hide *)

Lemma fsk_Tm_subst_tvar_Tm_lower_mutual :
(forall t1 t2 tx1,
  fsk_Tm t1 [<=] fsk_Tm (subst_tvar_Tm t2 tx1 t1)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fsk_Tm_subst_tvar_Tm_lower :
forall t1 t2 tx1,
  fsk_Tm t1 [<=] fsk_Tm (subst_tvar_Tm t2 tx1 t1).
Proof.
pose proof fsk_Tm_subst_tvar_Tm_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fsk_Tm_subst_tvar_Tm_lower : lngen.

(* begin hide *)

Lemma ftv_Tm_subst_skvar_Tm_lower_mutual :
(forall t1 T1 beta1,
  ftv_Tm t1 [<=] ftv_Tm (subst_skvar_Tm T1 beta1 t1)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_Tm_subst_skvar_Tm_lower :
forall t1 T1 beta1,
  ftv_Tm t1 [<=] ftv_Tm (subst_skvar_Tm T1 beta1 t1).
Proof.
pose proof ftv_Tm_subst_skvar_Tm_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_Tm_subst_skvar_Tm_lower : lngen.

(* begin hide *)

Lemma ftv_Tm_subst_tvar_Tm_lower_mutual :
(forall t1 t2 tx1,
  remove tx1 (ftv_Tm t1) [<=] ftv_Tm (subst_tvar_Tm t2 tx1 t1)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_Tm_subst_tvar_Tm_lower :
forall t1 t2 tx1,
  remove tx1 (ftv_Tm t1) [<=] ftv_Tm (subst_tvar_Tm t2 tx1 t1).
Proof.
pose proof ftv_Tm_subst_tvar_Tm_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_Tm_subst_tvar_Tm_lower : lngen.

(* begin hide *)

Lemma fv_Ex_subst_var_Ex_notin_mutual :
(forall e1 e2 x1 x2,
  x2 `notin` fv_Ex e1 ->
  x2 `notin` fv_Ex e2 ->
  x2 `notin` fv_Ex (subst_var_Ex e2 x1 e1)).
Proof.
apply_mutual_ind Ex_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_Ex_subst_var_Ex_notin :
forall e1 e2 x1 x2,
  x2 `notin` fv_Ex e1 ->
  x2 `notin` fv_Ex e2 ->
  x2 `notin` fv_Ex (subst_var_Ex e2 x1 e1).
Proof.
pose proof fv_Ex_subst_var_Ex_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_Ex_subst_var_Ex_notin : lngen.

(* begin hide *)

Lemma fsk_T_subst_skvar_T_notin_mutual :
(forall T1 T2 beta1 beta2,
  beta2 `notin` fsk_T T1 ->
  beta2 `notin` fsk_T T2 ->
  beta2 `notin` fsk_T (subst_skvar_T T2 beta1 T1)).
Proof.
apply_mutual_ind T_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fsk_T_subst_skvar_T_notin :
forall T1 T2 beta1 beta2,
  beta2 `notin` fsk_T T1 ->
  beta2 `notin` fsk_T T2 ->
  beta2 `notin` fsk_T (subst_skvar_T T2 beta1 T1).
Proof.
pose proof fsk_T_subst_skvar_T_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fsk_T_subst_skvar_T_notin : lngen.

(* begin hide *)

Lemma fsk_Sc_subst_skvar_Sc_notin_mutual :
(forall Sc1 T1 beta1 beta2,
  beta2 `notin` fsk_Sc Sc1 ->
  beta2 `notin` fsk_T T1 ->
  beta2 `notin` fsk_Sc (subst_skvar_Sc T1 beta1 Sc1)).
Proof.
apply_mutual_ind Sc_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fsk_Sc_subst_skvar_Sc_notin :
forall Sc1 T1 beta1 beta2,
  beta2 `notin` fsk_Sc Sc1 ->
  beta2 `notin` fsk_T T1 ->
  beta2 `notin` fsk_Sc (subst_skvar_Sc T1 beta1 Sc1).
Proof.
pose proof fsk_Sc_subst_skvar_Sc_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fsk_Sc_subst_skvar_Sc_notin : lngen.

(* begin hide *)

Lemma fsk_Tm_subst_skvar_Tm_notin_mutual :
(forall t1 T1 beta1 beta2,
  beta2 `notin` fsk_Tm t1 ->
  beta2 `notin` fsk_T T1 ->
  beta2 `notin` fsk_Tm (subst_skvar_Tm T1 beta1 t1)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fsk_Tm_subst_skvar_Tm_notin :
forall t1 T1 beta1 beta2,
  beta2 `notin` fsk_Tm t1 ->
  beta2 `notin` fsk_T T1 ->
  beta2 `notin` fsk_Tm (subst_skvar_Tm T1 beta1 t1).
Proof.
pose proof fsk_Tm_subst_skvar_Tm_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fsk_Tm_subst_skvar_Tm_notin : lngen.

(* begin hide *)

Lemma fsk_Tm_subst_tvar_Tm_notin_mutual :
(forall t1 t2 tx1 beta1,
  beta1 `notin` fsk_Tm t1 ->
  beta1 `notin` fsk_Tm t2 ->
  beta1 `notin` fsk_Tm (subst_tvar_Tm t2 tx1 t1)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fsk_Tm_subst_tvar_Tm_notin :
forall t1 t2 tx1 beta1,
  beta1 `notin` fsk_Tm t1 ->
  beta1 `notin` fsk_Tm t2 ->
  beta1 `notin` fsk_Tm (subst_tvar_Tm t2 tx1 t1).
Proof.
pose proof fsk_Tm_subst_tvar_Tm_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fsk_Tm_subst_tvar_Tm_notin : lngen.

(* begin hide *)

Lemma ftv_Tm_subst_skvar_Tm_notin_mutual :
(forall t1 T1 beta1 tx1,
  tx1 `notin` ftv_Tm t1 ->
  tx1 `notin` ftv_Tm (subst_skvar_Tm T1 beta1 t1)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_Tm_subst_skvar_Tm_notin :
forall t1 T1 beta1 tx1,
  tx1 `notin` ftv_Tm t1 ->
  tx1 `notin` ftv_Tm (subst_skvar_Tm T1 beta1 t1).
Proof.
pose proof ftv_Tm_subst_skvar_Tm_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_Tm_subst_skvar_Tm_notin : lngen.

(* begin hide *)

Lemma ftv_Tm_subst_tvar_Tm_notin_mutual :
(forall t1 t2 tx1 tx2,
  tx2 `notin` ftv_Tm t1 ->
  tx2 `notin` ftv_Tm t2 ->
  tx2 `notin` ftv_Tm (subst_tvar_Tm t2 tx1 t1)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_Tm_subst_tvar_Tm_notin :
forall t1 t2 tx1 tx2,
  tx2 `notin` ftv_Tm t1 ->
  tx2 `notin` ftv_Tm t2 ->
  tx2 `notin` ftv_Tm (subst_tvar_Tm t2 tx1 t1).
Proof.
pose proof ftv_Tm_subst_tvar_Tm_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_Tm_subst_tvar_Tm_notin : lngen.

(* begin hide *)

Lemma fv_Ex_subst_var_Ex_upper_mutual :
(forall e1 e2 x1,
  fv_Ex (subst_var_Ex e2 x1 e1) [<=] fv_Ex e2 `union` remove x1 (fv_Ex e1)).
Proof.
apply_mutual_ind Ex_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_Ex_subst_var_Ex_upper :
forall e1 e2 x1,
  fv_Ex (subst_var_Ex e2 x1 e1) [<=] fv_Ex e2 `union` remove x1 (fv_Ex e1).
Proof.
pose proof fv_Ex_subst_var_Ex_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_Ex_subst_var_Ex_upper : lngen.

(* begin hide *)

Lemma fsk_T_subst_skvar_T_upper_mutual :
(forall T1 T2 beta1,
  fsk_T (subst_skvar_T T2 beta1 T1) [<=] fsk_T T2 `union` remove beta1 (fsk_T T1)).
Proof.
apply_mutual_ind T_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fsk_T_subst_skvar_T_upper :
forall T1 T2 beta1,
  fsk_T (subst_skvar_T T2 beta1 T1) [<=] fsk_T T2 `union` remove beta1 (fsk_T T1).
Proof.
pose proof fsk_T_subst_skvar_T_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fsk_T_subst_skvar_T_upper : lngen.

(* begin hide *)

Lemma fsk_Sc_subst_skvar_Sc_upper_mutual :
(forall Sc1 T1 beta1,
  fsk_Sc (subst_skvar_Sc T1 beta1 Sc1) [<=] fsk_T T1 `union` remove beta1 (fsk_Sc Sc1)).
Proof.
apply_mutual_ind Sc_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fsk_Sc_subst_skvar_Sc_upper :
forall Sc1 T1 beta1,
  fsk_Sc (subst_skvar_Sc T1 beta1 Sc1) [<=] fsk_T T1 `union` remove beta1 (fsk_Sc Sc1).
Proof.
pose proof fsk_Sc_subst_skvar_Sc_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fsk_Sc_subst_skvar_Sc_upper : lngen.

(* begin hide *)

Lemma fsk_Tm_subst_skvar_Tm_upper_mutual :
(forall t1 T1 beta1,
  fsk_Tm (subst_skvar_Tm T1 beta1 t1) [<=] fsk_T T1 `union` remove beta1 (fsk_Tm t1)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fsk_Tm_subst_skvar_Tm_upper :
forall t1 T1 beta1,
  fsk_Tm (subst_skvar_Tm T1 beta1 t1) [<=] fsk_T T1 `union` remove beta1 (fsk_Tm t1).
Proof.
pose proof fsk_Tm_subst_skvar_Tm_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fsk_Tm_subst_skvar_Tm_upper : lngen.

(* begin hide *)

Lemma fsk_Tm_subst_tvar_Tm_upper_mutual :
(forall t1 t2 tx1,
  fsk_Tm (subst_tvar_Tm t2 tx1 t1) [<=] fsk_Tm t2 `union` fsk_Tm t1).
Proof.
apply_mutual_ind Tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fsk_Tm_subst_tvar_Tm_upper :
forall t1 t2 tx1,
  fsk_Tm (subst_tvar_Tm t2 tx1 t1) [<=] fsk_Tm t2 `union` fsk_Tm t1.
Proof.
pose proof fsk_Tm_subst_tvar_Tm_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fsk_Tm_subst_tvar_Tm_upper : lngen.

(* begin hide *)

Lemma ftv_Tm_subst_skvar_Tm_upper_mutual :
(forall t1 T1 beta1,
  ftv_Tm (subst_skvar_Tm T1 beta1 t1) [<=] ftv_Tm t1).
Proof.
apply_mutual_ind Tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_Tm_subst_skvar_Tm_upper :
forall t1 T1 beta1,
  ftv_Tm (subst_skvar_Tm T1 beta1 t1) [<=] ftv_Tm t1.
Proof.
pose proof ftv_Tm_subst_skvar_Tm_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_Tm_subst_skvar_Tm_upper : lngen.

(* begin hide *)

Lemma ftv_Tm_subst_tvar_Tm_upper_mutual :
(forall t1 t2 tx1,
  ftv_Tm (subst_tvar_Tm t2 tx1 t1) [<=] ftv_Tm t2 `union` remove tx1 (ftv_Tm t1)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_Tm_subst_tvar_Tm_upper :
forall t1 t2 tx1,
  ftv_Tm (subst_tvar_Tm t2 tx1 t1) [<=] ftv_Tm t2 `union` remove tx1 (ftv_Tm t1).
Proof.
pose proof ftv_Tm_subst_tvar_Tm_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_Tm_subst_tvar_Tm_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma subst_var_Ex_close_Ex_wrt_Ex_rec_mutual :
(forall e2 e1 x1 x2 n1,
  degree_Ex_wrt_Ex n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_Ex e1 ->
  subst_var_Ex e1 x1 (close_Ex_wrt_Ex_rec n1 x2 e2) = close_Ex_wrt_Ex_rec n1 x2 (subst_var_Ex e1 x1 e2)).
Proof.
apply_mutual_ind Ex_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_var_Ex_close_Ex_wrt_Ex_rec :
forall e2 e1 x1 x2 n1,
  degree_Ex_wrt_Ex n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_Ex e1 ->
  subst_var_Ex e1 x1 (close_Ex_wrt_Ex_rec n1 x2 e2) = close_Ex_wrt_Ex_rec n1 x2 (subst_var_Ex e1 x1 e2).
Proof.
pose proof subst_var_Ex_close_Ex_wrt_Ex_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_Ex_close_Ex_wrt_Ex_rec : lngen.

(* begin hide *)

Lemma subst_skvar_T_close_T_wrt_T_rec_mutual :
(forall T2 T1 beta1 beta2 n1,
  degree_T_wrt_T n1 T1 ->
  beta1 <> beta2 ->
  beta2 `notin` fsk_T T1 ->
  subst_skvar_T T1 beta1 (close_T_wrt_T_rec n1 beta2 T2) = close_T_wrt_T_rec n1 beta2 (subst_skvar_T T1 beta1 T2)).
Proof.
apply_mutual_ind T_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skvar_T_close_T_wrt_T_rec :
forall T2 T1 beta1 beta2 n1,
  degree_T_wrt_T n1 T1 ->
  beta1 <> beta2 ->
  beta2 `notin` fsk_T T1 ->
  subst_skvar_T T1 beta1 (close_T_wrt_T_rec n1 beta2 T2) = close_T_wrt_T_rec n1 beta2 (subst_skvar_T T1 beta1 T2).
Proof.
pose proof subst_skvar_T_close_T_wrt_T_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_T_close_T_wrt_T_rec : lngen.

(* begin hide *)

Lemma subst_skvar_Sc_close_Sc_wrt_T_rec_mutual :
(forall Sc1 T1 beta1 beta2 n1,
  degree_T_wrt_T n1 T1 ->
  beta1 <> beta2 ->
  beta2 `notin` fsk_T T1 ->
  subst_skvar_Sc T1 beta1 (close_Sc_wrt_T_rec n1 beta2 Sc1) = close_Sc_wrt_T_rec n1 beta2 (subst_skvar_Sc T1 beta1 Sc1)).
Proof.
apply_mutual_ind Sc_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skvar_Sc_close_Sc_wrt_T_rec :
forall Sc1 T1 beta1 beta2 n1,
  degree_T_wrt_T n1 T1 ->
  beta1 <> beta2 ->
  beta2 `notin` fsk_T T1 ->
  subst_skvar_Sc T1 beta1 (close_Sc_wrt_T_rec n1 beta2 Sc1) = close_Sc_wrt_T_rec n1 beta2 (subst_skvar_Sc T1 beta1 Sc1).
Proof.
pose proof subst_skvar_Sc_close_Sc_wrt_T_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Sc_close_Sc_wrt_T_rec : lngen.

(* begin hide *)

Lemma subst_skvar_Tm_close_Tm_wrt_T_rec_mutual :
(forall t1 T1 beta1 beta2 n1,
  degree_T_wrt_T n1 T1 ->
  beta1 <> beta2 ->
  beta2 `notin` fsk_T T1 ->
  subst_skvar_Tm T1 beta1 (close_Tm_wrt_T_rec n1 beta2 t1) = close_Tm_wrt_T_rec n1 beta2 (subst_skvar_Tm T1 beta1 t1)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skvar_Tm_close_Tm_wrt_T_rec :
forall t1 T1 beta1 beta2 n1,
  degree_T_wrt_T n1 T1 ->
  beta1 <> beta2 ->
  beta2 `notin` fsk_T T1 ->
  subst_skvar_Tm T1 beta1 (close_Tm_wrt_T_rec n1 beta2 t1) = close_Tm_wrt_T_rec n1 beta2 (subst_skvar_Tm T1 beta1 t1).
Proof.
pose proof subst_skvar_Tm_close_Tm_wrt_T_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Tm_close_Tm_wrt_T_rec : lngen.

(* begin hide *)

Lemma subst_skvar_Tm_close_Tm_wrt_Tm_rec_mutual :
(forall t1 T1 tx1 beta1 n1,
  subst_skvar_Tm T1 tx1 (close_Tm_wrt_Tm_rec n1 beta1 t1) = close_Tm_wrt_Tm_rec n1 beta1 (subst_skvar_Tm T1 tx1 t1)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skvar_Tm_close_Tm_wrt_Tm_rec :
forall t1 T1 tx1 beta1 n1,
  subst_skvar_Tm T1 tx1 (close_Tm_wrt_Tm_rec n1 beta1 t1) = close_Tm_wrt_Tm_rec n1 beta1 (subst_skvar_Tm T1 tx1 t1).
Proof.
pose proof subst_skvar_Tm_close_Tm_wrt_Tm_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Tm_close_Tm_wrt_Tm_rec : lngen.

(* begin hide *)

Lemma subst_tvar_Tm_close_Tm_wrt_T_rec_mutual :
(forall t2 t1 beta1 tx1 n1,
  degree_Tm_wrt_T n1 t1 ->
  tx1 `notin` fsk_Tm t1 ->
  subst_tvar_Tm t1 beta1 (close_Tm_wrt_T_rec n1 tx1 t2) = close_Tm_wrt_T_rec n1 tx1 (subst_tvar_Tm t1 beta1 t2)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_Tm_close_Tm_wrt_T_rec :
forall t2 t1 beta1 tx1 n1,
  degree_Tm_wrt_T n1 t1 ->
  tx1 `notin` fsk_Tm t1 ->
  subst_tvar_Tm t1 beta1 (close_Tm_wrt_T_rec n1 tx1 t2) = close_Tm_wrt_T_rec n1 tx1 (subst_tvar_Tm t1 beta1 t2).
Proof.
pose proof subst_tvar_Tm_close_Tm_wrt_T_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_Tm_close_Tm_wrt_T_rec : lngen.

(* begin hide *)

Lemma subst_tvar_Tm_close_Tm_wrt_Tm_rec_mutual :
(forall t2 t1 tx1 tx2 n1,
  degree_Tm_wrt_Tm n1 t1 ->
  tx1 <> tx2 ->
  tx2 `notin` ftv_Tm t1 ->
  subst_tvar_Tm t1 tx1 (close_Tm_wrt_Tm_rec n1 tx2 t2) = close_Tm_wrt_Tm_rec n1 tx2 (subst_tvar_Tm t1 tx1 t2)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_Tm_close_Tm_wrt_Tm_rec :
forall t2 t1 tx1 tx2 n1,
  degree_Tm_wrt_Tm n1 t1 ->
  tx1 <> tx2 ->
  tx2 `notin` ftv_Tm t1 ->
  subst_tvar_Tm t1 tx1 (close_Tm_wrt_Tm_rec n1 tx2 t2) = close_Tm_wrt_Tm_rec n1 tx2 (subst_tvar_Tm t1 tx1 t2).
Proof.
pose proof subst_tvar_Tm_close_Tm_wrt_Tm_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_Tm_close_Tm_wrt_Tm_rec : lngen.

Lemma subst_var_Ex_close_Ex_wrt_Ex :
forall e2 e1 x1 x2,
  lc_Ex e1 ->  x1 <> x2 ->
  x2 `notin` fv_Ex e1 ->
  subst_var_Ex e1 x1 (close_Ex_wrt_Ex x2 e2) = close_Ex_wrt_Ex x2 (subst_var_Ex e1 x1 e2).
Proof.
unfold close_Ex_wrt_Ex; default_simp.
Qed.

#[export] Hint Resolve subst_var_Ex_close_Ex_wrt_Ex : lngen.

Lemma subst_skvar_T_close_T_wrt_T :
forall T2 T1 beta1 beta2,
  lc_T T1 ->  beta1 <> beta2 ->
  beta2 `notin` fsk_T T1 ->
  subst_skvar_T T1 beta1 (close_T_wrt_T beta2 T2) = close_T_wrt_T beta2 (subst_skvar_T T1 beta1 T2).
Proof.
unfold close_T_wrt_T; default_simp.
Qed.

#[export] Hint Resolve subst_skvar_T_close_T_wrt_T : lngen.

Lemma subst_skvar_Sc_close_Sc_wrt_T :
forall Sc1 T1 beta1 beta2,
  lc_T T1 ->  beta1 <> beta2 ->
  beta2 `notin` fsk_T T1 ->
  subst_skvar_Sc T1 beta1 (close_Sc_wrt_T beta2 Sc1) = close_Sc_wrt_T beta2 (subst_skvar_Sc T1 beta1 Sc1).
Proof.
unfold close_Sc_wrt_T; default_simp.
Qed.

#[export] Hint Resolve subst_skvar_Sc_close_Sc_wrt_T : lngen.

Lemma subst_skvar_Tm_close_Tm_wrt_T :
forall t1 T1 beta1 beta2,
  lc_T T1 ->  beta1 <> beta2 ->
  beta2 `notin` fsk_T T1 ->
  subst_skvar_Tm T1 beta1 (close_Tm_wrt_T beta2 t1) = close_Tm_wrt_T beta2 (subst_skvar_Tm T1 beta1 t1).
Proof.
unfold close_Tm_wrt_T; default_simp.
Qed.

#[export] Hint Resolve subst_skvar_Tm_close_Tm_wrt_T : lngen.

Lemma subst_skvar_Tm_close_Tm_wrt_Tm :
forall t1 T1 tx1 beta1,
  lc_T T1 ->  subst_skvar_Tm T1 tx1 (close_Tm_wrt_Tm beta1 t1) = close_Tm_wrt_Tm beta1 (subst_skvar_Tm T1 tx1 t1).
Proof.
unfold close_Tm_wrt_Tm; default_simp.
Qed.

#[export] Hint Resolve subst_skvar_Tm_close_Tm_wrt_Tm : lngen.

Lemma subst_tvar_Tm_close_Tm_wrt_T :
forall t2 t1 beta1 tx1,
  lc_Tm t1 ->  tx1 `notin` fsk_Tm t1 ->
  subst_tvar_Tm t1 beta1 (close_Tm_wrt_T tx1 t2) = close_Tm_wrt_T tx1 (subst_tvar_Tm t1 beta1 t2).
Proof.
unfold close_Tm_wrt_T; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_Tm_close_Tm_wrt_T : lngen.

Lemma subst_tvar_Tm_close_Tm_wrt_Tm :
forall t2 t1 tx1 tx2,
  lc_Tm t1 ->  tx1 <> tx2 ->
  tx2 `notin` ftv_Tm t1 ->
  subst_tvar_Tm t1 tx1 (close_Tm_wrt_Tm tx2 t2) = close_Tm_wrt_Tm tx2 (subst_tvar_Tm t1 tx1 t2).
Proof.
unfold close_Tm_wrt_Tm; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_Tm_close_Tm_wrt_Tm : lngen.

(* begin hide *)

Lemma subst_var_Ex_degree_Ex_wrt_Ex_mutual :
(forall e1 e2 x1 n1,
  degree_Ex_wrt_Ex n1 e1 ->
  degree_Ex_wrt_Ex n1 e2 ->
  degree_Ex_wrt_Ex n1 (subst_var_Ex e2 x1 e1)).
Proof.
apply_mutual_ind Ex_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_var_Ex_degree_Ex_wrt_Ex :
forall e1 e2 x1 n1,
  degree_Ex_wrt_Ex n1 e1 ->
  degree_Ex_wrt_Ex n1 e2 ->
  degree_Ex_wrt_Ex n1 (subst_var_Ex e2 x1 e1).
Proof.
pose proof subst_var_Ex_degree_Ex_wrt_Ex_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_Ex_degree_Ex_wrt_Ex : lngen.

(* begin hide *)

Lemma subst_skvar_T_degree_T_wrt_T_mutual :
(forall T1 T2 beta1 n1,
  degree_T_wrt_T n1 T1 ->
  degree_T_wrt_T n1 T2 ->
  degree_T_wrt_T n1 (subst_skvar_T T2 beta1 T1)).
Proof.
apply_mutual_ind T_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skvar_T_degree_T_wrt_T :
forall T1 T2 beta1 n1,
  degree_T_wrt_T n1 T1 ->
  degree_T_wrt_T n1 T2 ->
  degree_T_wrt_T n1 (subst_skvar_T T2 beta1 T1).
Proof.
pose proof subst_skvar_T_degree_T_wrt_T_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_T_degree_T_wrt_T : lngen.

(* begin hide *)

Lemma subst_skvar_Sc_degree_Sc_wrt_T_mutual :
(forall Sc1 T1 beta1 n1,
  degree_Sc_wrt_T n1 Sc1 ->
  degree_T_wrt_T n1 T1 ->
  degree_Sc_wrt_T n1 (subst_skvar_Sc T1 beta1 Sc1)).
Proof.
apply_mutual_ind Sc_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skvar_Sc_degree_Sc_wrt_T :
forall Sc1 T1 beta1 n1,
  degree_Sc_wrt_T n1 Sc1 ->
  degree_T_wrt_T n1 T1 ->
  degree_Sc_wrt_T n1 (subst_skvar_Sc T1 beta1 Sc1).
Proof.
pose proof subst_skvar_Sc_degree_Sc_wrt_T_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Sc_degree_Sc_wrt_T : lngen.

(* begin hide *)

Lemma subst_skvar_Tm_degree_Tm_wrt_T_mutual :
(forall t1 T1 beta1 n1,
  degree_Tm_wrt_T n1 t1 ->
  degree_T_wrt_T n1 T1 ->
  degree_Tm_wrt_T n1 (subst_skvar_Tm T1 beta1 t1)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skvar_Tm_degree_Tm_wrt_T :
forall t1 T1 beta1 n1,
  degree_Tm_wrt_T n1 t1 ->
  degree_T_wrt_T n1 T1 ->
  degree_Tm_wrt_T n1 (subst_skvar_Tm T1 beta1 t1).
Proof.
pose proof subst_skvar_Tm_degree_Tm_wrt_T_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Tm_degree_Tm_wrt_T : lngen.

(* begin hide *)

Lemma subst_skvar_Tm_degree_Tm_wrt_Tm_mutual :
(forall t1 T1 beta1 n1,
  degree_Tm_wrt_Tm n1 t1 ->
  degree_Tm_wrt_Tm n1 (subst_skvar_Tm T1 beta1 t1)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skvar_Tm_degree_Tm_wrt_Tm :
forall t1 T1 beta1 n1,
  degree_Tm_wrt_Tm n1 t1 ->
  degree_Tm_wrt_Tm n1 (subst_skvar_Tm T1 beta1 t1).
Proof.
pose proof subst_skvar_Tm_degree_Tm_wrt_Tm_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Tm_degree_Tm_wrt_Tm : lngen.

(* begin hide *)

Lemma subst_tvar_Tm_degree_Tm_wrt_T_mutual :
(forall t1 t2 tx1 n1,
  degree_Tm_wrt_T n1 t1 ->
  degree_Tm_wrt_T n1 t2 ->
  degree_Tm_wrt_T n1 (subst_tvar_Tm t2 tx1 t1)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_Tm_degree_Tm_wrt_T :
forall t1 t2 tx1 n1,
  degree_Tm_wrt_T n1 t1 ->
  degree_Tm_wrt_T n1 t2 ->
  degree_Tm_wrt_T n1 (subst_tvar_Tm t2 tx1 t1).
Proof.
pose proof subst_tvar_Tm_degree_Tm_wrt_T_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_Tm_degree_Tm_wrt_T : lngen.

(* begin hide *)

Lemma subst_tvar_Tm_degree_Tm_wrt_Tm_mutual :
(forall t1 t2 tx1 n1,
  degree_Tm_wrt_Tm n1 t1 ->
  degree_Tm_wrt_Tm n1 t2 ->
  degree_Tm_wrt_Tm n1 (subst_tvar_Tm t2 tx1 t1)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_Tm_degree_Tm_wrt_Tm :
forall t1 t2 tx1 n1,
  degree_Tm_wrt_Tm n1 t1 ->
  degree_Tm_wrt_Tm n1 t2 ->
  degree_Tm_wrt_Tm n1 (subst_tvar_Tm t2 tx1 t1).
Proof.
pose proof subst_tvar_Tm_degree_Tm_wrt_Tm_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_Tm_degree_Tm_wrt_Tm : lngen.

(* begin hide *)

Lemma subst_var_Ex_fresh_eq_mutual :
(forall e2 e1 x1,
  x1 `notin` fv_Ex e2 ->
  subst_var_Ex e1 x1 e2 = e2).
Proof.
apply_mutual_ind Ex_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_var_Ex_fresh_eq :
forall e2 e1 x1,
  x1 `notin` fv_Ex e2 ->
  subst_var_Ex e1 x1 e2 = e2.
Proof.
pose proof subst_var_Ex_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_Ex_fresh_eq : lngen.
#[export] Hint Rewrite subst_var_Ex_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_skvar_T_fresh_eq_mutual :
(forall T2 T1 beta1,
  beta1 `notin` fsk_T T2 ->
  subst_skvar_T T1 beta1 T2 = T2).
Proof.
apply_mutual_ind T_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skvar_T_fresh_eq :
forall T2 T1 beta1,
  beta1 `notin` fsk_T T2 ->
  subst_skvar_T T1 beta1 T2 = T2.
Proof.
pose proof subst_skvar_T_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_T_fresh_eq : lngen.
#[export] Hint Rewrite subst_skvar_T_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_skvar_Sc_fresh_eq_mutual :
(forall Sc1 T1 beta1,
  beta1 `notin` fsk_Sc Sc1 ->
  subst_skvar_Sc T1 beta1 Sc1 = Sc1).
Proof.
apply_mutual_ind Sc_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skvar_Sc_fresh_eq :
forall Sc1 T1 beta1,
  beta1 `notin` fsk_Sc Sc1 ->
  subst_skvar_Sc T1 beta1 Sc1 = Sc1.
Proof.
pose proof subst_skvar_Sc_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Sc_fresh_eq : lngen.
#[export] Hint Rewrite subst_skvar_Sc_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_skvar_Tm_fresh_eq_mutual :
(forall t1 T1 beta1,
  beta1 `notin` fsk_Tm t1 ->
  subst_skvar_Tm T1 beta1 t1 = t1).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skvar_Tm_fresh_eq :
forall t1 T1 beta1,
  beta1 `notin` fsk_Tm t1 ->
  subst_skvar_Tm T1 beta1 t1 = t1.
Proof.
pose proof subst_skvar_Tm_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Tm_fresh_eq : lngen.
#[export] Hint Rewrite subst_skvar_Tm_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_tvar_Tm_fresh_eq_mutual :
(forall t2 t1 tx1,
  tx1 `notin` ftv_Tm t2 ->
  subst_tvar_Tm t1 tx1 t2 = t2).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_Tm_fresh_eq :
forall t2 t1 tx1,
  tx1 `notin` ftv_Tm t2 ->
  subst_tvar_Tm t1 tx1 t2 = t2.
Proof.
pose proof subst_tvar_Tm_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_Tm_fresh_eq : lngen.
#[export] Hint Rewrite subst_tvar_Tm_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_var_Ex_fresh_same_mutual :
(forall e2 e1 x1,
  x1 `notin` fv_Ex e1 ->
  x1 `notin` fv_Ex (subst_var_Ex e1 x1 e2)).
Proof.
apply_mutual_ind Ex_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_var_Ex_fresh_same :
forall e2 e1 x1,
  x1 `notin` fv_Ex e1 ->
  x1 `notin` fv_Ex (subst_var_Ex e1 x1 e2).
Proof.
pose proof subst_var_Ex_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_Ex_fresh_same : lngen.

(* begin hide *)

Lemma subst_skvar_T_fresh_same_mutual :
(forall T2 T1 beta1,
  beta1 `notin` fsk_T T1 ->
  beta1 `notin` fsk_T (subst_skvar_T T1 beta1 T2)).
Proof.
apply_mutual_ind T_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skvar_T_fresh_same :
forall T2 T1 beta1,
  beta1 `notin` fsk_T T1 ->
  beta1 `notin` fsk_T (subst_skvar_T T1 beta1 T2).
Proof.
pose proof subst_skvar_T_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_T_fresh_same : lngen.

(* begin hide *)

Lemma subst_skvar_Sc_fresh_same_mutual :
(forall Sc1 T1 beta1,
  beta1 `notin` fsk_T T1 ->
  beta1 `notin` fsk_Sc (subst_skvar_Sc T1 beta1 Sc1)).
Proof.
apply_mutual_ind Sc_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skvar_Sc_fresh_same :
forall Sc1 T1 beta1,
  beta1 `notin` fsk_T T1 ->
  beta1 `notin` fsk_Sc (subst_skvar_Sc T1 beta1 Sc1).
Proof.
pose proof subst_skvar_Sc_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Sc_fresh_same : lngen.

(* begin hide *)

Lemma subst_skvar_Tm_fresh_same_mutual :
(forall t1 T1 beta1,
  beta1 `notin` fsk_T T1 ->
  beta1 `notin` fsk_Tm (subst_skvar_Tm T1 beta1 t1)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skvar_Tm_fresh_same :
forall t1 T1 beta1,
  beta1 `notin` fsk_T T1 ->
  beta1 `notin` fsk_Tm (subst_skvar_Tm T1 beta1 t1).
Proof.
pose proof subst_skvar_Tm_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Tm_fresh_same : lngen.

(* begin hide *)

Lemma subst_tvar_Tm_fresh_same_mutual :
(forall t2 t1 tx1,
  tx1 `notin` ftv_Tm t1 ->
  tx1 `notin` ftv_Tm (subst_tvar_Tm t1 tx1 t2)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_Tm_fresh_same :
forall t2 t1 tx1,
  tx1 `notin` ftv_Tm t1 ->
  tx1 `notin` ftv_Tm (subst_tvar_Tm t1 tx1 t2).
Proof.
pose proof subst_tvar_Tm_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_Tm_fresh_same : lngen.

(* begin hide *)

Lemma subst_var_Ex_fresh_mutual :
(forall e2 e1 x1 x2,
  x1 `notin` fv_Ex e2 ->
  x1 `notin` fv_Ex e1 ->
  x1 `notin` fv_Ex (subst_var_Ex e1 x2 e2)).
Proof.
apply_mutual_ind Ex_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_var_Ex_fresh :
forall e2 e1 x1 x2,
  x1 `notin` fv_Ex e2 ->
  x1 `notin` fv_Ex e1 ->
  x1 `notin` fv_Ex (subst_var_Ex e1 x2 e2).
Proof.
pose proof subst_var_Ex_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_Ex_fresh : lngen.

(* begin hide *)

Lemma subst_skvar_T_fresh_mutual :
(forall T2 T1 beta1 beta2,
  beta1 `notin` fsk_T T2 ->
  beta1 `notin` fsk_T T1 ->
  beta1 `notin` fsk_T (subst_skvar_T T1 beta2 T2)).
Proof.
apply_mutual_ind T_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skvar_T_fresh :
forall T2 T1 beta1 beta2,
  beta1 `notin` fsk_T T2 ->
  beta1 `notin` fsk_T T1 ->
  beta1 `notin` fsk_T (subst_skvar_T T1 beta2 T2).
Proof.
pose proof subst_skvar_T_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_T_fresh : lngen.

(* begin hide *)

Lemma subst_skvar_Sc_fresh_mutual :
(forall Sc1 T1 beta1 beta2,
  beta1 `notin` fsk_Sc Sc1 ->
  beta1 `notin` fsk_T T1 ->
  beta1 `notin` fsk_Sc (subst_skvar_Sc T1 beta2 Sc1)).
Proof.
apply_mutual_ind Sc_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skvar_Sc_fresh :
forall Sc1 T1 beta1 beta2,
  beta1 `notin` fsk_Sc Sc1 ->
  beta1 `notin` fsk_T T1 ->
  beta1 `notin` fsk_Sc (subst_skvar_Sc T1 beta2 Sc1).
Proof.
pose proof subst_skvar_Sc_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Sc_fresh : lngen.

(* begin hide *)

Lemma subst_skvar_Tm_fresh_mutual :
(forall t1 T1 beta1 beta2,
  beta1 `notin` fsk_Tm t1 ->
  beta1 `notin` fsk_T T1 ->
  beta1 `notin` fsk_Tm (subst_skvar_Tm T1 beta2 t1)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skvar_Tm_fresh :
forall t1 T1 beta1 beta2,
  beta1 `notin` fsk_Tm t1 ->
  beta1 `notin` fsk_T T1 ->
  beta1 `notin` fsk_Tm (subst_skvar_Tm T1 beta2 t1).
Proof.
pose proof subst_skvar_Tm_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Tm_fresh : lngen.

(* begin hide *)

Lemma subst_tvar_Tm_fresh_mutual :
(forall t2 t1 tx1 tx2,
  tx1 `notin` ftv_Tm t2 ->
  tx1 `notin` ftv_Tm t1 ->
  tx1 `notin` ftv_Tm (subst_tvar_Tm t1 tx2 t2)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_Tm_fresh :
forall t2 t1 tx1 tx2,
  tx1 `notin` ftv_Tm t2 ->
  tx1 `notin` ftv_Tm t1 ->
  tx1 `notin` ftv_Tm (subst_tvar_Tm t1 tx2 t2).
Proof.
pose proof subst_tvar_Tm_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_Tm_fresh : lngen.

Lemma subst_var_Ex_lc_Ex :
forall e1 e2 x1,
  lc_Ex e1 ->
  lc_Ex e2 ->
  lc_Ex (subst_var_Ex e2 x1 e1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_var_Ex_lc_Ex : lngen.

Lemma subst_skvar_T_lc_T :
forall T1 T2 beta1,
  lc_T T1 ->
  lc_T T2 ->
  lc_T (subst_skvar_T T2 beta1 T1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_skvar_T_lc_T : lngen.

Lemma subst_skvar_Sc_lc_Sc :
forall Sc1 T1 beta1,
  lc_Sc Sc1 ->
  lc_T T1 ->
  lc_Sc (subst_skvar_Sc T1 beta1 Sc1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_skvar_Sc_lc_Sc : lngen.

Lemma subst_skvar_Tm_lc_Tm :
forall t1 T1 beta1,
  lc_Tm t1 ->
  lc_T T1 ->
  lc_Tm (subst_skvar_Tm T1 beta1 t1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_skvar_Tm_lc_Tm : lngen.

Lemma subst_tvar_Tm_lc_Tm :
forall t1 t2 tx1,
  lc_Tm t1 ->
  lc_Tm t2 ->
  lc_Tm (subst_tvar_Tm t2 tx1 t1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_tvar_Tm_lc_Tm : lngen.

(* begin hide *)

Lemma subst_var_Ex_open_Ex_wrt_Ex_rec_mutual :
(forall e3 e1 e2 x1 n1,
  lc_Ex e1 ->
  subst_var_Ex e1 x1 (open_Ex_wrt_Ex_rec n1 e2 e3) = open_Ex_wrt_Ex_rec n1 (subst_var_Ex e1 x1 e2) (subst_var_Ex e1 x1 e3)).
Proof.
apply_mutual_ind Ex_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_var_Ex_open_Ex_wrt_Ex_rec :
forall e3 e1 e2 x1 n1,
  lc_Ex e1 ->
  subst_var_Ex e1 x1 (open_Ex_wrt_Ex_rec n1 e2 e3) = open_Ex_wrt_Ex_rec n1 (subst_var_Ex e1 x1 e2) (subst_var_Ex e1 x1 e3).
Proof.
pose proof subst_var_Ex_open_Ex_wrt_Ex_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_Ex_open_Ex_wrt_Ex_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_skvar_T_open_T_wrt_T_rec_mutual :
(forall T3 T1 T2 beta1 n1,
  lc_T T1 ->
  subst_skvar_T T1 beta1 (open_T_wrt_T_rec n1 T2 T3) = open_T_wrt_T_rec n1 (subst_skvar_T T1 beta1 T2) (subst_skvar_T T1 beta1 T3)).
Proof.
apply_mutual_ind T_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_skvar_T_open_T_wrt_T_rec :
forall T3 T1 T2 beta1 n1,
  lc_T T1 ->
  subst_skvar_T T1 beta1 (open_T_wrt_T_rec n1 T2 T3) = open_T_wrt_T_rec n1 (subst_skvar_T T1 beta1 T2) (subst_skvar_T T1 beta1 T3).
Proof.
pose proof subst_skvar_T_open_T_wrt_T_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_T_open_T_wrt_T_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_skvar_Sc_open_Sc_wrt_T_rec_mutual :
(forall Sc1 T1 T2 beta1 n1,
  lc_T T1 ->
  subst_skvar_Sc T1 beta1 (open_Sc_wrt_T_rec n1 T2 Sc1) = open_Sc_wrt_T_rec n1 (subst_skvar_T T1 beta1 T2) (subst_skvar_Sc T1 beta1 Sc1)).
Proof.
apply_mutual_ind Sc_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_skvar_Sc_open_Sc_wrt_T_rec :
forall Sc1 T1 T2 beta1 n1,
  lc_T T1 ->
  subst_skvar_Sc T1 beta1 (open_Sc_wrt_T_rec n1 T2 Sc1) = open_Sc_wrt_T_rec n1 (subst_skvar_T T1 beta1 T2) (subst_skvar_Sc T1 beta1 Sc1).
Proof.
pose proof subst_skvar_Sc_open_Sc_wrt_T_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Sc_open_Sc_wrt_T_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_skvar_Tm_open_Tm_wrt_T_rec_mutual :
(forall t1 T1 T2 beta1 n1,
  lc_T T1 ->
  subst_skvar_Tm T1 beta1 (open_Tm_wrt_T_rec n1 T2 t1) = open_Tm_wrt_T_rec n1 (subst_skvar_T T1 beta1 T2) (subst_skvar_Tm T1 beta1 t1)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_skvar_Tm_open_Tm_wrt_T_rec :
forall t1 T1 T2 beta1 n1,
  lc_T T1 ->
  subst_skvar_Tm T1 beta1 (open_Tm_wrt_T_rec n1 T2 t1) = open_Tm_wrt_T_rec n1 (subst_skvar_T T1 beta1 T2) (subst_skvar_Tm T1 beta1 t1).
Proof.
pose proof subst_skvar_Tm_open_Tm_wrt_T_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Tm_open_Tm_wrt_T_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_skvar_Tm_open_Tm_wrt_Tm_rec_mutual :
(forall t2 T1 t1 beta1 n1,
  subst_skvar_Tm T1 beta1 (open_Tm_wrt_Tm_rec n1 t1 t2) = open_Tm_wrt_Tm_rec n1 (subst_skvar_Tm T1 beta1 t1) (subst_skvar_Tm T1 beta1 t2)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_skvar_Tm_open_Tm_wrt_Tm_rec :
forall t2 T1 t1 beta1 n1,
  subst_skvar_Tm T1 beta1 (open_Tm_wrt_Tm_rec n1 t1 t2) = open_Tm_wrt_Tm_rec n1 (subst_skvar_Tm T1 beta1 t1) (subst_skvar_Tm T1 beta1 t2).
Proof.
pose proof subst_skvar_Tm_open_Tm_wrt_Tm_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Tm_open_Tm_wrt_Tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_Tm_open_Tm_wrt_T_rec_mutual :
(forall t2 t1 T1 tx1 n1,
  lc_Tm t1 ->
  subst_tvar_Tm t1 tx1 (open_Tm_wrt_T_rec n1 T1 t2) = open_Tm_wrt_T_rec n1 T1 (subst_tvar_Tm t1 tx1 t2)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_Tm_open_Tm_wrt_T_rec :
forall t2 t1 T1 tx1 n1,
  lc_Tm t1 ->
  subst_tvar_Tm t1 tx1 (open_Tm_wrt_T_rec n1 T1 t2) = open_Tm_wrt_T_rec n1 T1 (subst_tvar_Tm t1 tx1 t2).
Proof.
pose proof subst_tvar_Tm_open_Tm_wrt_T_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_Tm_open_Tm_wrt_T_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_Tm_open_Tm_wrt_Tm_rec_mutual :
(forall t3 t1 t2 tx1 n1,
  lc_Tm t1 ->
  subst_tvar_Tm t1 tx1 (open_Tm_wrt_Tm_rec n1 t2 t3) = open_Tm_wrt_Tm_rec n1 (subst_tvar_Tm t1 tx1 t2) (subst_tvar_Tm t1 tx1 t3)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_Tm_open_Tm_wrt_Tm_rec :
forall t3 t1 t2 tx1 n1,
  lc_Tm t1 ->
  subst_tvar_Tm t1 tx1 (open_Tm_wrt_Tm_rec n1 t2 t3) = open_Tm_wrt_Tm_rec n1 (subst_tvar_Tm t1 tx1 t2) (subst_tvar_Tm t1 tx1 t3).
Proof.
pose proof subst_tvar_Tm_open_Tm_wrt_Tm_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_Tm_open_Tm_wrt_Tm_rec : lngen.

(* end hide *)

Lemma subst_var_Ex_open_Ex_wrt_Ex :
forall e3 e1 e2 x1,
  lc_Ex e1 ->
  subst_var_Ex e1 x1 (open_Ex_wrt_Ex e3 e2) = open_Ex_wrt_Ex (subst_var_Ex e1 x1 e3) (subst_var_Ex e1 x1 e2).
Proof.
unfold open_Ex_wrt_Ex; default_simp.
Qed.

#[export] Hint Resolve subst_var_Ex_open_Ex_wrt_Ex : lngen.

Lemma subst_skvar_T_open_T_wrt_T :
forall T3 T1 T2 beta1,
  lc_T T1 ->
  subst_skvar_T T1 beta1 (open_T_wrt_T T3 T2) = open_T_wrt_T (subst_skvar_T T1 beta1 T3) (subst_skvar_T T1 beta1 T2).
Proof.
unfold open_T_wrt_T; default_simp.
Qed.

#[export] Hint Resolve subst_skvar_T_open_T_wrt_T : lngen.

Lemma subst_skvar_Sc_open_Sc_wrt_T :
forall Sc1 T1 T2 beta1,
  lc_T T1 ->
  subst_skvar_Sc T1 beta1 (open_Sc_wrt_T Sc1 T2) = open_Sc_wrt_T (subst_skvar_Sc T1 beta1 Sc1) (subst_skvar_T T1 beta1 T2).
Proof.
unfold open_Sc_wrt_T; default_simp.
Qed.

#[export] Hint Resolve subst_skvar_Sc_open_Sc_wrt_T : lngen.

Lemma subst_skvar_Tm_open_Tm_wrt_T :
forall t1 T1 T2 beta1,
  lc_T T1 ->
  subst_skvar_Tm T1 beta1 (open_Tm_wrt_T t1 T2) = open_Tm_wrt_T (subst_skvar_Tm T1 beta1 t1) (subst_skvar_T T1 beta1 T2).
Proof.
unfold open_Tm_wrt_T; default_simp.
Qed.

#[export] Hint Resolve subst_skvar_Tm_open_Tm_wrt_T : lngen.

Lemma subst_skvar_Tm_open_Tm_wrt_Tm :
forall t2 T1 t1 beta1,
  subst_skvar_Tm T1 beta1 (open_Tm_wrt_Tm t2 t1) = open_Tm_wrt_Tm (subst_skvar_Tm T1 beta1 t2) (subst_skvar_Tm T1 beta1 t1).
Proof.
unfold open_Tm_wrt_Tm; default_simp.
Qed.

#[export] Hint Resolve subst_skvar_Tm_open_Tm_wrt_Tm : lngen.

Lemma subst_tvar_Tm_open_Tm_wrt_T :
forall t2 t1 T1 tx1,
  lc_Tm t1 ->
  subst_tvar_Tm t1 tx1 (open_Tm_wrt_T t2 T1) = open_Tm_wrt_T (subst_tvar_Tm t1 tx1 t2) T1.
Proof.
unfold open_Tm_wrt_T; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_Tm_open_Tm_wrt_T : lngen.

Lemma subst_tvar_Tm_open_Tm_wrt_Tm :
forall t3 t1 t2 tx1,
  lc_Tm t1 ->
  subst_tvar_Tm t1 tx1 (open_Tm_wrt_Tm t3 t2) = open_Tm_wrt_Tm (subst_tvar_Tm t1 tx1 t3) (subst_tvar_Tm t1 tx1 t2).
Proof.
unfold open_Tm_wrt_Tm; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_Tm_open_Tm_wrt_Tm : lngen.

Lemma subst_var_Ex_open_Ex_wrt_Ex_var :
forall e2 e1 x1 x2,
  x1 <> x2 ->
  lc_Ex e1 ->
  open_Ex_wrt_Ex (subst_var_Ex e1 x1 e2) (e__Var_f x2) = subst_var_Ex e1 x1 (open_Ex_wrt_Ex e2 (e__Var_f x2)).
Proof.
intros; rewrite subst_var_Ex_open_Ex_wrt_Ex; default_simp.
Qed.

#[export] Hint Resolve subst_var_Ex_open_Ex_wrt_Ex_var : lngen.

Lemma subst_skvar_T_open_T_wrt_T_var :
forall T2 T1 beta1 beta2,
  beta1 <> beta2 ->
  lc_T T1 ->
  open_T_wrt_T (subst_skvar_T T1 beta1 T2) (T__Var_f beta2) = subst_skvar_T T1 beta1 (open_T_wrt_T T2 (T__Var_f beta2)).
Proof.
intros; rewrite subst_skvar_T_open_T_wrt_T; default_simp.
Qed.

#[export] Hint Resolve subst_skvar_T_open_T_wrt_T_var : lngen.

Lemma subst_skvar_Sc_open_Sc_wrt_T_var :
forall Sc1 T1 beta1 beta2,
  beta1 <> beta2 ->
  lc_T T1 ->
  open_Sc_wrt_T (subst_skvar_Sc T1 beta1 Sc1) (T__Var_f beta2) = subst_skvar_Sc T1 beta1 (open_Sc_wrt_T Sc1 (T__Var_f beta2)).
Proof.
intros; rewrite subst_skvar_Sc_open_Sc_wrt_T; default_simp.
Qed.

#[export] Hint Resolve subst_skvar_Sc_open_Sc_wrt_T_var : lngen.

Lemma subst_skvar_Tm_open_Tm_wrt_T_var :
forall t1 T1 beta1 beta2,
  beta1 <> beta2 ->
  lc_T T1 ->
  open_Tm_wrt_T (subst_skvar_Tm T1 beta1 t1) (T__Var_f beta2) = subst_skvar_Tm T1 beta1 (open_Tm_wrt_T t1 (T__Var_f beta2)).
Proof.
intros; rewrite subst_skvar_Tm_open_Tm_wrt_T; default_simp.
Qed.

#[export] Hint Resolve subst_skvar_Tm_open_Tm_wrt_T_var : lngen.

Lemma subst_skvar_Tm_open_Tm_wrt_Tm_var :
forall t1 T1 beta1 tx1,
  open_Tm_wrt_Tm (subst_skvar_Tm T1 beta1 t1) (t__Var_f tx1) = subst_skvar_Tm T1 beta1 (open_Tm_wrt_Tm t1 (t__Var_f tx1)).
Proof.
intros; rewrite subst_skvar_Tm_open_Tm_wrt_Tm; default_simp.
Qed.

#[export] Hint Resolve subst_skvar_Tm_open_Tm_wrt_Tm_var : lngen.

Lemma subst_tvar_Tm_open_Tm_wrt_T_var :
forall t2 t1 tx1 beta1,
  lc_Tm t1 ->
  open_Tm_wrt_T (subst_tvar_Tm t1 tx1 t2) (T__Var_f beta1) = subst_tvar_Tm t1 tx1 (open_Tm_wrt_T t2 (T__Var_f beta1)).
Proof.
intros; rewrite subst_tvar_Tm_open_Tm_wrt_T; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_Tm_open_Tm_wrt_T_var : lngen.

Lemma subst_tvar_Tm_open_Tm_wrt_Tm_var :
forall t2 t1 tx1 tx2,
  tx1 <> tx2 ->
  lc_Tm t1 ->
  open_Tm_wrt_Tm (subst_tvar_Tm t1 tx1 t2) (t__Var_f tx2) = subst_tvar_Tm t1 tx1 (open_Tm_wrt_Tm t2 (t__Var_f tx2)).
Proof.
intros; rewrite subst_tvar_Tm_open_Tm_wrt_Tm; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_Tm_open_Tm_wrt_Tm_var : lngen.

(* begin hide *)

Lemma subst_var_Ex_spec_rec_mutual :
(forall e1 e2 x1 n1,
  subst_var_Ex e2 x1 e1 = open_Ex_wrt_Ex_rec n1 e2 (close_Ex_wrt_Ex_rec n1 x1 e1)).
Proof.
apply_mutual_ind Ex_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_var_Ex_spec_rec :
forall e1 e2 x1 n1,
  subst_var_Ex e2 x1 e1 = open_Ex_wrt_Ex_rec n1 e2 (close_Ex_wrt_Ex_rec n1 x1 e1).
Proof.
pose proof subst_var_Ex_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_Ex_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_skvar_T_spec_rec_mutual :
(forall T1 T2 beta1 n1,
  subst_skvar_T T2 beta1 T1 = open_T_wrt_T_rec n1 T2 (close_T_wrt_T_rec n1 beta1 T1)).
Proof.
apply_mutual_ind T_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_skvar_T_spec_rec :
forall T1 T2 beta1 n1,
  subst_skvar_T T2 beta1 T1 = open_T_wrt_T_rec n1 T2 (close_T_wrt_T_rec n1 beta1 T1).
Proof.
pose proof subst_skvar_T_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_T_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_skvar_Sc_spec_rec_mutual :
(forall Sc1 T1 beta1 n1,
  subst_skvar_Sc T1 beta1 Sc1 = open_Sc_wrt_T_rec n1 T1 (close_Sc_wrt_T_rec n1 beta1 Sc1)).
Proof.
apply_mutual_ind Sc_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_skvar_Sc_spec_rec :
forall Sc1 T1 beta1 n1,
  subst_skvar_Sc T1 beta1 Sc1 = open_Sc_wrt_T_rec n1 T1 (close_Sc_wrt_T_rec n1 beta1 Sc1).
Proof.
pose proof subst_skvar_Sc_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Sc_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_skvar_Tm_spec_rec_mutual :
(forall t1 T1 beta1 n1,
  subst_skvar_Tm T1 beta1 t1 = open_Tm_wrt_T_rec n1 T1 (close_Tm_wrt_T_rec n1 beta1 t1)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_skvar_Tm_spec_rec :
forall t1 T1 beta1 n1,
  subst_skvar_Tm T1 beta1 t1 = open_Tm_wrt_T_rec n1 T1 (close_Tm_wrt_T_rec n1 beta1 t1).
Proof.
pose proof subst_skvar_Tm_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Tm_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_Tm_spec_rec_mutual :
(forall t1 t2 tx1 n1,
  subst_tvar_Tm t2 tx1 t1 = open_Tm_wrt_Tm_rec n1 t2 (close_Tm_wrt_Tm_rec n1 tx1 t1)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_Tm_spec_rec :
forall t1 t2 tx1 n1,
  subst_tvar_Tm t2 tx1 t1 = open_Tm_wrt_Tm_rec n1 t2 (close_Tm_wrt_Tm_rec n1 tx1 t1).
Proof.
pose proof subst_tvar_Tm_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_Tm_spec_rec : lngen.

(* end hide *)

Lemma subst_var_Ex_spec :
forall e1 e2 x1,
  subst_var_Ex e2 x1 e1 = open_Ex_wrt_Ex (close_Ex_wrt_Ex x1 e1) e2.
Proof.
unfold close_Ex_wrt_Ex; unfold open_Ex_wrt_Ex; default_simp.
Qed.

#[export] Hint Resolve subst_var_Ex_spec : lngen.

Lemma subst_skvar_T_spec :
forall T1 T2 beta1,
  subst_skvar_T T2 beta1 T1 = open_T_wrt_T (close_T_wrt_T beta1 T1) T2.
Proof.
unfold close_T_wrt_T; unfold open_T_wrt_T; default_simp.
Qed.

#[export] Hint Resolve subst_skvar_T_spec : lngen.

Lemma subst_skvar_Sc_spec :
forall Sc1 T1 beta1,
  subst_skvar_Sc T1 beta1 Sc1 = open_Sc_wrt_T (close_Sc_wrt_T beta1 Sc1) T1.
Proof.
unfold close_Sc_wrt_T; unfold open_Sc_wrt_T; default_simp.
Qed.

#[export] Hint Resolve subst_skvar_Sc_spec : lngen.

Lemma subst_skvar_Tm_spec :
forall t1 T1 beta1,
  subst_skvar_Tm T1 beta1 t1 = open_Tm_wrt_T (close_Tm_wrt_T beta1 t1) T1.
Proof.
unfold close_Tm_wrt_T; unfold open_Tm_wrt_T; default_simp.
Qed.

#[export] Hint Resolve subst_skvar_Tm_spec : lngen.

Lemma subst_tvar_Tm_spec :
forall t1 t2 tx1,
  subst_tvar_Tm t2 tx1 t1 = open_Tm_wrt_Tm (close_Tm_wrt_Tm tx1 t1) t2.
Proof.
unfold close_Tm_wrt_Tm; unfold open_Tm_wrt_Tm; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_Tm_spec : lngen.

(* begin hide *)

Lemma subst_var_Ex_subst_var_Ex_mutual :
(forall e1 e2 e3 x2 x1,
  x2 `notin` fv_Ex e2 ->
  x2 <> x1 ->
  subst_var_Ex e2 x1 (subst_var_Ex e3 x2 e1) = subst_var_Ex (subst_var_Ex e2 x1 e3) x2 (subst_var_Ex e2 x1 e1)).
Proof.
apply_mutual_ind Ex_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_var_Ex_subst_var_Ex :
forall e1 e2 e3 x2 x1,
  x2 `notin` fv_Ex e2 ->
  x2 <> x1 ->
  subst_var_Ex e2 x1 (subst_var_Ex e3 x2 e1) = subst_var_Ex (subst_var_Ex e2 x1 e3) x2 (subst_var_Ex e2 x1 e1).
Proof.
pose proof subst_var_Ex_subst_var_Ex_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_Ex_subst_var_Ex : lngen.

(* begin hide *)

Lemma subst_skvar_T_subst_skvar_T_mutual :
(forall T1 T2 T3 beta2 beta1,
  beta2 `notin` fsk_T T2 ->
  beta2 <> beta1 ->
  subst_skvar_T T2 beta1 (subst_skvar_T T3 beta2 T1) = subst_skvar_T (subst_skvar_T T2 beta1 T3) beta2 (subst_skvar_T T2 beta1 T1)).
Proof.
apply_mutual_ind T_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skvar_T_subst_skvar_T :
forall T1 T2 T3 beta2 beta1,
  beta2 `notin` fsk_T T2 ->
  beta2 <> beta1 ->
  subst_skvar_T T2 beta1 (subst_skvar_T T3 beta2 T1) = subst_skvar_T (subst_skvar_T T2 beta1 T3) beta2 (subst_skvar_T T2 beta1 T1).
Proof.
pose proof subst_skvar_T_subst_skvar_T_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_T_subst_skvar_T : lngen.

(* begin hide *)

Lemma subst_skvar_Sc_subst_skvar_Sc_mutual :
(forall Sc1 T1 T2 beta2 beta1,
  beta2 `notin` fsk_T T1 ->
  beta2 <> beta1 ->
  subst_skvar_Sc T1 beta1 (subst_skvar_Sc T2 beta2 Sc1) = subst_skvar_Sc (subst_skvar_T T1 beta1 T2) beta2 (subst_skvar_Sc T1 beta1 Sc1)).
Proof.
apply_mutual_ind Sc_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skvar_Sc_subst_skvar_Sc :
forall Sc1 T1 T2 beta2 beta1,
  beta2 `notin` fsk_T T1 ->
  beta2 <> beta1 ->
  subst_skvar_Sc T1 beta1 (subst_skvar_Sc T2 beta2 Sc1) = subst_skvar_Sc (subst_skvar_T T1 beta1 T2) beta2 (subst_skvar_Sc T1 beta1 Sc1).
Proof.
pose proof subst_skvar_Sc_subst_skvar_Sc_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Sc_subst_skvar_Sc : lngen.

(* begin hide *)

Lemma subst_skvar_Tm_subst_skvar_Tm_mutual :
(forall t1 T1 T2 beta2 beta1,
  beta2 `notin` fsk_T T1 ->
  beta2 <> beta1 ->
  subst_skvar_Tm T1 beta1 (subst_skvar_Tm T2 beta2 t1) = subst_skvar_Tm (subst_skvar_T T1 beta1 T2) beta2 (subst_skvar_Tm T1 beta1 t1)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skvar_Tm_subst_skvar_Tm :
forall t1 T1 T2 beta2 beta1,
  beta2 `notin` fsk_T T1 ->
  beta2 <> beta1 ->
  subst_skvar_Tm T1 beta1 (subst_skvar_Tm T2 beta2 t1) = subst_skvar_Tm (subst_skvar_T T1 beta1 T2) beta2 (subst_skvar_Tm T1 beta1 t1).
Proof.
pose proof subst_skvar_Tm_subst_skvar_Tm_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Tm_subst_skvar_Tm : lngen.

(* begin hide *)

Lemma subst_skvar_Tm_subst_tvar_Tm_mutual :
(forall t1 T1 t2 tx1 beta1,
  subst_skvar_Tm T1 beta1 (subst_tvar_Tm t2 tx1 t1) = subst_tvar_Tm (subst_skvar_Tm T1 beta1 t2) tx1 (subst_skvar_Tm T1 beta1 t1)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skvar_Tm_subst_tvar_Tm :
forall t1 T1 t2 tx1 beta1,
  subst_skvar_Tm T1 beta1 (subst_tvar_Tm t2 tx1 t1) = subst_tvar_Tm (subst_skvar_Tm T1 beta1 t2) tx1 (subst_skvar_Tm T1 beta1 t1).
Proof.
pose proof subst_skvar_Tm_subst_tvar_Tm_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Tm_subst_tvar_Tm : lngen.

(* begin hide *)

Lemma subst_tvar_Tm_subst_skvar_Tm_mutual :
(forall t1 t2 T1 beta1 tx1,
  beta1 `notin` fsk_Tm t2 ->
  subst_tvar_Tm t2 tx1 (subst_skvar_Tm T1 beta1 t1) = subst_skvar_Tm T1 beta1 (subst_tvar_Tm t2 tx1 t1)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_Tm_subst_skvar_Tm :
forall t1 t2 T1 beta1 tx1,
  beta1 `notin` fsk_Tm t2 ->
  subst_tvar_Tm t2 tx1 (subst_skvar_Tm T1 beta1 t1) = subst_skvar_Tm T1 beta1 (subst_tvar_Tm t2 tx1 t1).
Proof.
pose proof subst_tvar_Tm_subst_skvar_Tm_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_Tm_subst_skvar_Tm : lngen.

(* begin hide *)

Lemma subst_tvar_Tm_subst_tvar_Tm_mutual :
(forall t1 t2 t3 tx2 tx1,
  tx2 `notin` ftv_Tm t2 ->
  tx2 <> tx1 ->
  subst_tvar_Tm t2 tx1 (subst_tvar_Tm t3 tx2 t1) = subst_tvar_Tm (subst_tvar_Tm t2 tx1 t3) tx2 (subst_tvar_Tm t2 tx1 t1)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_Tm_subst_tvar_Tm :
forall t1 t2 t3 tx2 tx1,
  tx2 `notin` ftv_Tm t2 ->
  tx2 <> tx1 ->
  subst_tvar_Tm t2 tx1 (subst_tvar_Tm t3 tx2 t1) = subst_tvar_Tm (subst_tvar_Tm t2 tx1 t3) tx2 (subst_tvar_Tm t2 tx1 t1).
Proof.
pose proof subst_tvar_Tm_subst_tvar_Tm_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_Tm_subst_tvar_Tm : lngen.

(* begin hide *)

Lemma subst_var_Ex_close_Ex_wrt_Ex_rec_open_Ex_wrt_Ex_rec_mutual :
(forall e2 e1 x1 x2 n1,
  x2 `notin` fv_Ex e2 ->
  x2 `notin` fv_Ex e1 ->
  x2 <> x1 ->
  degree_Ex_wrt_Ex n1 e1 ->
  subst_var_Ex e1 x1 e2 = close_Ex_wrt_Ex_rec n1 x2 (subst_var_Ex e1 x1 (open_Ex_wrt_Ex_rec n1 (e__Var_f x2) e2))).
Proof.
apply_mutual_ind Ex_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_var_Ex_close_Ex_wrt_Ex_rec_open_Ex_wrt_Ex_rec :
forall e2 e1 x1 x2 n1,
  x2 `notin` fv_Ex e2 ->
  x2 `notin` fv_Ex e1 ->
  x2 <> x1 ->
  degree_Ex_wrt_Ex n1 e1 ->
  subst_var_Ex e1 x1 e2 = close_Ex_wrt_Ex_rec n1 x2 (subst_var_Ex e1 x1 (open_Ex_wrt_Ex_rec n1 (e__Var_f x2) e2)).
Proof.
pose proof subst_var_Ex_close_Ex_wrt_Ex_rec_open_Ex_wrt_Ex_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_Ex_close_Ex_wrt_Ex_rec_open_Ex_wrt_Ex_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_skvar_T_close_T_wrt_T_rec_open_T_wrt_T_rec_mutual :
(forall T2 T1 beta1 beta2 n1,
  beta2 `notin` fsk_T T2 ->
  beta2 `notin` fsk_T T1 ->
  beta2 <> beta1 ->
  degree_T_wrt_T n1 T1 ->
  subst_skvar_T T1 beta1 T2 = close_T_wrt_T_rec n1 beta2 (subst_skvar_T T1 beta1 (open_T_wrt_T_rec n1 (T__Var_f beta2) T2))).
Proof.
apply_mutual_ind T_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_skvar_T_close_T_wrt_T_rec_open_T_wrt_T_rec :
forall T2 T1 beta1 beta2 n1,
  beta2 `notin` fsk_T T2 ->
  beta2 `notin` fsk_T T1 ->
  beta2 <> beta1 ->
  degree_T_wrt_T n1 T1 ->
  subst_skvar_T T1 beta1 T2 = close_T_wrt_T_rec n1 beta2 (subst_skvar_T T1 beta1 (open_T_wrt_T_rec n1 (T__Var_f beta2) T2)).
Proof.
pose proof subst_skvar_T_close_T_wrt_T_rec_open_T_wrt_T_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_T_close_T_wrt_T_rec_open_T_wrt_T_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_skvar_Sc_close_Sc_wrt_T_rec_open_Sc_wrt_T_rec_mutual :
(forall Sc1 T1 beta1 beta2 n1,
  beta2 `notin` fsk_Sc Sc1 ->
  beta2 `notin` fsk_T T1 ->
  beta2 <> beta1 ->
  degree_T_wrt_T n1 T1 ->
  subst_skvar_Sc T1 beta1 Sc1 = close_Sc_wrt_T_rec n1 beta2 (subst_skvar_Sc T1 beta1 (open_Sc_wrt_T_rec n1 (T__Var_f beta2) Sc1))).
Proof.
apply_mutual_ind Sc_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_skvar_Sc_close_Sc_wrt_T_rec_open_Sc_wrt_T_rec :
forall Sc1 T1 beta1 beta2 n1,
  beta2 `notin` fsk_Sc Sc1 ->
  beta2 `notin` fsk_T T1 ->
  beta2 <> beta1 ->
  degree_T_wrt_T n1 T1 ->
  subst_skvar_Sc T1 beta1 Sc1 = close_Sc_wrt_T_rec n1 beta2 (subst_skvar_Sc T1 beta1 (open_Sc_wrt_T_rec n1 (T__Var_f beta2) Sc1)).
Proof.
pose proof subst_skvar_Sc_close_Sc_wrt_T_rec_open_Sc_wrt_T_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Sc_close_Sc_wrt_T_rec_open_Sc_wrt_T_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_skvar_Tm_close_Tm_wrt_T_rec_open_Tm_wrt_T_rec_mutual :
(forall t1 T1 beta1 beta2 n1,
  beta2 `notin` fsk_Tm t1 ->
  beta2 `notin` fsk_T T1 ->
  beta2 <> beta1 ->
  degree_T_wrt_T n1 T1 ->
  subst_skvar_Tm T1 beta1 t1 = close_Tm_wrt_T_rec n1 beta2 (subst_skvar_Tm T1 beta1 (open_Tm_wrt_T_rec n1 (T__Var_f beta2) t1))).
Proof.
apply_mutual_ind Tm_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_skvar_Tm_close_Tm_wrt_T_rec_open_Tm_wrt_T_rec :
forall t1 T1 beta1 beta2 n1,
  beta2 `notin` fsk_Tm t1 ->
  beta2 `notin` fsk_T T1 ->
  beta2 <> beta1 ->
  degree_T_wrt_T n1 T1 ->
  subst_skvar_Tm T1 beta1 t1 = close_Tm_wrt_T_rec n1 beta2 (subst_skvar_Tm T1 beta1 (open_Tm_wrt_T_rec n1 (T__Var_f beta2) t1)).
Proof.
pose proof subst_skvar_Tm_close_Tm_wrt_T_rec_open_Tm_wrt_T_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Tm_close_Tm_wrt_T_rec_open_Tm_wrt_T_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_skvar_Tm_close_Tm_wrt_Tm_rec_open_Tm_wrt_Tm_rec_mutual :
(forall t1 T1 beta1 tx1 n1,
  tx1 `notin` ftv_Tm t1 ->
  subst_skvar_Tm T1 beta1 t1 = close_Tm_wrt_Tm_rec n1 tx1 (subst_skvar_Tm T1 beta1 (open_Tm_wrt_Tm_rec n1 (t__Var_f tx1) t1))).
Proof.
apply_mutual_ind Tm_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_skvar_Tm_close_Tm_wrt_Tm_rec_open_Tm_wrt_Tm_rec :
forall t1 T1 beta1 tx1 n1,
  tx1 `notin` ftv_Tm t1 ->
  subst_skvar_Tm T1 beta1 t1 = close_Tm_wrt_Tm_rec n1 tx1 (subst_skvar_Tm T1 beta1 (open_Tm_wrt_Tm_rec n1 (t__Var_f tx1) t1)).
Proof.
pose proof subst_skvar_Tm_close_Tm_wrt_Tm_rec_open_Tm_wrt_Tm_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Tm_close_Tm_wrt_Tm_rec_open_Tm_wrt_Tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_Tm_close_Tm_wrt_T_rec_open_Tm_wrt_T_rec_mutual :
(forall t2 t1 tx1 beta1 n1,
  beta1 `notin` fsk_Tm t2 ->
  beta1 `notin` fsk_Tm t1 ->
  degree_Tm_wrt_T n1 t1 ->
  subst_tvar_Tm t1 tx1 t2 = close_Tm_wrt_T_rec n1 beta1 (subst_tvar_Tm t1 tx1 (open_Tm_wrt_T_rec n1 (T__Var_f beta1) t2))).
Proof.
apply_mutual_ind Tm_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_Tm_close_Tm_wrt_T_rec_open_Tm_wrt_T_rec :
forall t2 t1 tx1 beta1 n1,
  beta1 `notin` fsk_Tm t2 ->
  beta1 `notin` fsk_Tm t1 ->
  degree_Tm_wrt_T n1 t1 ->
  subst_tvar_Tm t1 tx1 t2 = close_Tm_wrt_T_rec n1 beta1 (subst_tvar_Tm t1 tx1 (open_Tm_wrt_T_rec n1 (T__Var_f beta1) t2)).
Proof.
pose proof subst_tvar_Tm_close_Tm_wrt_T_rec_open_Tm_wrt_T_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_Tm_close_Tm_wrt_T_rec_open_Tm_wrt_T_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_Tm_close_Tm_wrt_Tm_rec_open_Tm_wrt_Tm_rec_mutual :
(forall t2 t1 tx1 tx2 n1,
  tx2 `notin` ftv_Tm t2 ->
  tx2 `notin` ftv_Tm t1 ->
  tx2 <> tx1 ->
  degree_Tm_wrt_Tm n1 t1 ->
  subst_tvar_Tm t1 tx1 t2 = close_Tm_wrt_Tm_rec n1 tx2 (subst_tvar_Tm t1 tx1 (open_Tm_wrt_Tm_rec n1 (t__Var_f tx2) t2))).
Proof.
apply_mutual_ind Tm_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_Tm_close_Tm_wrt_Tm_rec_open_Tm_wrt_Tm_rec :
forall t2 t1 tx1 tx2 n1,
  tx2 `notin` ftv_Tm t2 ->
  tx2 `notin` ftv_Tm t1 ->
  tx2 <> tx1 ->
  degree_Tm_wrt_Tm n1 t1 ->
  subst_tvar_Tm t1 tx1 t2 = close_Tm_wrt_Tm_rec n1 tx2 (subst_tvar_Tm t1 tx1 (open_Tm_wrt_Tm_rec n1 (t__Var_f tx2) t2)).
Proof.
pose proof subst_tvar_Tm_close_Tm_wrt_Tm_rec_open_Tm_wrt_Tm_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_Tm_close_Tm_wrt_Tm_rec_open_Tm_wrt_Tm_rec : lngen.

(* end hide *)

Lemma subst_var_Ex_close_Ex_wrt_Ex_open_Ex_wrt_Ex :
forall e2 e1 x1 x2,
  x2 `notin` fv_Ex e2 ->
  x2 `notin` fv_Ex e1 ->
  x2 <> x1 ->
  lc_Ex e1 ->
  subst_var_Ex e1 x1 e2 = close_Ex_wrt_Ex x2 (subst_var_Ex e1 x1 (open_Ex_wrt_Ex e2 (e__Var_f x2))).
Proof.
unfold close_Ex_wrt_Ex; unfold open_Ex_wrt_Ex; default_simp.
Qed.

#[export] Hint Resolve subst_var_Ex_close_Ex_wrt_Ex_open_Ex_wrt_Ex : lngen.

Lemma subst_skvar_T_close_T_wrt_T_open_T_wrt_T :
forall T2 T1 beta1 beta2,
  beta2 `notin` fsk_T T2 ->
  beta2 `notin` fsk_T T1 ->
  beta2 <> beta1 ->
  lc_T T1 ->
  subst_skvar_T T1 beta1 T2 = close_T_wrt_T beta2 (subst_skvar_T T1 beta1 (open_T_wrt_T T2 (T__Var_f beta2))).
Proof.
unfold close_T_wrt_T; unfold open_T_wrt_T; default_simp.
Qed.

#[export] Hint Resolve subst_skvar_T_close_T_wrt_T_open_T_wrt_T : lngen.

Lemma subst_skvar_Sc_close_Sc_wrt_T_open_Sc_wrt_T :
forall Sc1 T1 beta1 beta2,
  beta2 `notin` fsk_Sc Sc1 ->
  beta2 `notin` fsk_T T1 ->
  beta2 <> beta1 ->
  lc_T T1 ->
  subst_skvar_Sc T1 beta1 Sc1 = close_Sc_wrt_T beta2 (subst_skvar_Sc T1 beta1 (open_Sc_wrt_T Sc1 (T__Var_f beta2))).
Proof.
unfold close_Sc_wrt_T; unfold open_Sc_wrt_T; default_simp.
Qed.

#[export] Hint Resolve subst_skvar_Sc_close_Sc_wrt_T_open_Sc_wrt_T : lngen.

Lemma subst_skvar_Tm_close_Tm_wrt_T_open_Tm_wrt_T :
forall t1 T1 beta1 beta2,
  beta2 `notin` fsk_Tm t1 ->
  beta2 `notin` fsk_T T1 ->
  beta2 <> beta1 ->
  lc_T T1 ->
  subst_skvar_Tm T1 beta1 t1 = close_Tm_wrt_T beta2 (subst_skvar_Tm T1 beta1 (open_Tm_wrt_T t1 (T__Var_f beta2))).
Proof.
unfold close_Tm_wrt_T; unfold open_Tm_wrt_T; default_simp.
Qed.

#[export] Hint Resolve subst_skvar_Tm_close_Tm_wrt_T_open_Tm_wrt_T : lngen.

Lemma subst_skvar_Tm_close_Tm_wrt_Tm_open_Tm_wrt_Tm :
forall t1 T1 beta1 tx1,
  tx1 `notin` ftv_Tm t1 ->
  lc_T T1 ->
  subst_skvar_Tm T1 beta1 t1 = close_Tm_wrt_Tm tx1 (subst_skvar_Tm T1 beta1 (open_Tm_wrt_Tm t1 (t__Var_f tx1))).
Proof.
unfold close_Tm_wrt_Tm; unfold open_Tm_wrt_Tm; default_simp.
Qed.

#[export] Hint Resolve subst_skvar_Tm_close_Tm_wrt_Tm_open_Tm_wrt_Tm : lngen.

Lemma subst_tvar_Tm_close_Tm_wrt_T_open_Tm_wrt_T :
forall t2 t1 tx1 beta1,
  beta1 `notin` fsk_Tm t2 ->
  beta1 `notin` fsk_Tm t1 ->
  lc_Tm t1 ->
  subst_tvar_Tm t1 tx1 t2 = close_Tm_wrt_T beta1 (subst_tvar_Tm t1 tx1 (open_Tm_wrt_T t2 (T__Var_f beta1))).
Proof.
unfold close_Tm_wrt_T; unfold open_Tm_wrt_T; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_Tm_close_Tm_wrt_T_open_Tm_wrt_T : lngen.

Lemma subst_tvar_Tm_close_Tm_wrt_Tm_open_Tm_wrt_Tm :
forall t2 t1 tx1 tx2,
  tx2 `notin` ftv_Tm t2 ->
  tx2 `notin` ftv_Tm t1 ->
  tx2 <> tx1 ->
  lc_Tm t1 ->
  subst_tvar_Tm t1 tx1 t2 = close_Tm_wrt_Tm tx2 (subst_tvar_Tm t1 tx1 (open_Tm_wrt_Tm t2 (t__Var_f tx2))).
Proof.
unfold close_Tm_wrt_Tm; unfold open_Tm_wrt_Tm; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_Tm_close_Tm_wrt_Tm_open_Tm_wrt_Tm : lngen.

Lemma subst_var_Ex_e__Lam :
forall x2 e2 e1 x1,
  lc_Ex e1 ->
  x2 `notin` fv_Ex e1 `union` fv_Ex e2 `union` singleton x1 ->
  subst_var_Ex e1 x1 (e__Lam e2) = e__Lam (close_Ex_wrt_Ex x2 (subst_var_Ex e1 x1 (open_Ex_wrt_Ex e2 (e__Var_f x2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_var_Ex_e__Lam : lngen.

Lemma subst_var_Ex_e__Let :
forall x2 e2 e3 e1 x1,
  lc_Ex e1 ->
  x2 `notin` fv_Ex e1 `union` fv_Ex e3 `union` singleton x1 ->
  subst_var_Ex e1 x1 (e__Let e2 e3) = e__Let (subst_var_Ex e1 x1 e2) (close_Ex_wrt_Ex x2 (subst_var_Ex e1 x1 (open_Ex_wrt_Ex e3 (e__Var_f x2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_var_Ex_e__Let : lngen.

Lemma subst_skvar_Sc_S__Forall :
forall alpha1 sigma1 T1 beta1,
  lc_T T1 ->
  alpha1 `notin` fsk_T T1 `union` fsk_Sc sigma1 `union` singleton beta1 ->
  subst_skvar_Sc T1 beta1 (S__Forall sigma1) = S__Forall (close_Sc_wrt_T alpha1 (subst_skvar_Sc T1 beta1 (open_Sc_wrt_T sigma1 (T__Var_f alpha1)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_skvar_Sc_S__Forall : lngen.

Lemma subst_skvar_Tm_t__Lam :
forall tx1 tau1 t1 T1 beta1,
  lc_T T1 ->
  tx1 `notin` ftv_Tm t1 ->
  subst_skvar_Tm T1 beta1 (t__Lam tau1 t1) = t__Lam (subst_skvar_T T1 beta1 tau1) (close_Tm_wrt_Tm tx1 (subst_skvar_Tm T1 beta1 (open_Tm_wrt_Tm t1 (t__Var_f tx1)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_skvar_Tm_t__Lam : lngen.

Lemma subst_skvar_Tm_t__TLam :
forall alpha1 t1 T1 beta1,
  lc_T T1 ->
  alpha1 `notin` fsk_T T1 `union` fsk_Tm t1 `union` singleton beta1 ->
  subst_skvar_Tm T1 beta1 (t__TLam t1) = t__TLam (close_Tm_wrt_T alpha1 (subst_skvar_Tm T1 beta1 (open_Tm_wrt_T t1 (T__Var_f alpha1)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_skvar_Tm_t__TLam : lngen.

Lemma subst_tvar_Tm_t__Lam :
forall tx2 tau1 t2 t1 tx1,
  lc_Tm t1 ->
  tx2 `notin` ftv_Tm t1 `union` ftv_Tm t2 `union` singleton tx1 ->
  subst_tvar_Tm t1 tx1 (t__Lam tau1 t2) = t__Lam (tau1) (close_Tm_wrt_Tm tx2 (subst_tvar_Tm t1 tx1 (open_Tm_wrt_Tm t2 (t__Var_f tx2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_tvar_Tm_t__Lam : lngen.

Lemma subst_tvar_Tm_t__TLam :
forall alpha1 t2 t1 tx1,
  lc_Tm t1 ->
  alpha1 `notin` fsk_Tm t1 `union` fsk_Tm t2 ->
  subst_tvar_Tm t1 tx1 (t__TLam t2) = t__TLam (close_Tm_wrt_T alpha1 (subst_tvar_Tm t1 tx1 (open_Tm_wrt_T t2 (T__Var_f alpha1)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_tvar_Tm_t__TLam : lngen.

(* begin hide *)

Lemma subst_var_Ex_intro_rec_mutual :
(forall e1 x1 e2 n1,
  x1 `notin` fv_Ex e1 ->
  open_Ex_wrt_Ex_rec n1 e2 e1 = subst_var_Ex e2 x1 (open_Ex_wrt_Ex_rec n1 (e__Var_f x1) e1)).
Proof.
apply_mutual_ind Ex_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_var_Ex_intro_rec :
forall e1 x1 e2 n1,
  x1 `notin` fv_Ex e1 ->
  open_Ex_wrt_Ex_rec n1 e2 e1 = subst_var_Ex e2 x1 (open_Ex_wrt_Ex_rec n1 (e__Var_f x1) e1).
Proof.
pose proof subst_var_Ex_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_Ex_intro_rec : lngen.
#[export] Hint Rewrite subst_var_Ex_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_skvar_T_intro_rec_mutual :
(forall T1 beta1 T2 n1,
  beta1 `notin` fsk_T T1 ->
  open_T_wrt_T_rec n1 T2 T1 = subst_skvar_T T2 beta1 (open_T_wrt_T_rec n1 (T__Var_f beta1) T1)).
Proof.
apply_mutual_ind T_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skvar_T_intro_rec :
forall T1 beta1 T2 n1,
  beta1 `notin` fsk_T T1 ->
  open_T_wrt_T_rec n1 T2 T1 = subst_skvar_T T2 beta1 (open_T_wrt_T_rec n1 (T__Var_f beta1) T1).
Proof.
pose proof subst_skvar_T_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_T_intro_rec : lngen.
#[export] Hint Rewrite subst_skvar_T_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_skvar_Sc_intro_rec_mutual :
(forall Sc1 beta1 T1 n1,
  beta1 `notin` fsk_Sc Sc1 ->
  open_Sc_wrt_T_rec n1 T1 Sc1 = subst_skvar_Sc T1 beta1 (open_Sc_wrt_T_rec n1 (T__Var_f beta1) Sc1)).
Proof.
apply_mutual_ind Sc_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skvar_Sc_intro_rec :
forall Sc1 beta1 T1 n1,
  beta1 `notin` fsk_Sc Sc1 ->
  open_Sc_wrt_T_rec n1 T1 Sc1 = subst_skvar_Sc T1 beta1 (open_Sc_wrt_T_rec n1 (T__Var_f beta1) Sc1).
Proof.
pose proof subst_skvar_Sc_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Sc_intro_rec : lngen.
#[export] Hint Rewrite subst_skvar_Sc_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_skvar_Tm_intro_rec_mutual :
(forall t1 beta1 T1 n1,
  beta1 `notin` fsk_Tm t1 ->
  open_Tm_wrt_T_rec n1 T1 t1 = subst_skvar_Tm T1 beta1 (open_Tm_wrt_T_rec n1 (T__Var_f beta1) t1)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skvar_Tm_intro_rec :
forall t1 beta1 T1 n1,
  beta1 `notin` fsk_Tm t1 ->
  open_Tm_wrt_T_rec n1 T1 t1 = subst_skvar_Tm T1 beta1 (open_Tm_wrt_T_rec n1 (T__Var_f beta1) t1).
Proof.
pose proof subst_skvar_Tm_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skvar_Tm_intro_rec : lngen.
#[export] Hint Rewrite subst_skvar_Tm_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_tvar_Tm_intro_rec_mutual :
(forall t1 tx1 t2 n1,
  tx1 `notin` ftv_Tm t1 ->
  open_Tm_wrt_Tm_rec n1 t2 t1 = subst_tvar_Tm t2 tx1 (open_Tm_wrt_Tm_rec n1 (t__Var_f tx1) t1)).
Proof.
apply_mutual_ind Tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_Tm_intro_rec :
forall t1 tx1 t2 n1,
  tx1 `notin` ftv_Tm t1 ->
  open_Tm_wrt_Tm_rec n1 t2 t1 = subst_tvar_Tm t2 tx1 (open_Tm_wrt_Tm_rec n1 (t__Var_f tx1) t1).
Proof.
pose proof subst_tvar_Tm_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_Tm_intro_rec : lngen.
#[export] Hint Rewrite subst_tvar_Tm_intro_rec using solve [auto] : lngen.

Lemma subst_var_Ex_intro :
forall x1 e1 e2,
  x1 `notin` fv_Ex e1 ->
  open_Ex_wrt_Ex e1 e2 = subst_var_Ex e2 x1 (open_Ex_wrt_Ex e1 (e__Var_f x1)).
Proof.
unfold open_Ex_wrt_Ex; default_simp.
Qed.

#[export] Hint Resolve subst_var_Ex_intro : lngen.

Lemma subst_skvar_T_intro :
forall beta1 T1 T2,
  beta1 `notin` fsk_T T1 ->
  open_T_wrt_T T1 T2 = subst_skvar_T T2 beta1 (open_T_wrt_T T1 (T__Var_f beta1)).
Proof.
unfold open_T_wrt_T; default_simp.
Qed.

#[export] Hint Resolve subst_skvar_T_intro : lngen.

Lemma subst_skvar_Sc_intro :
forall beta1 Sc1 T1,
  beta1 `notin` fsk_Sc Sc1 ->
  open_Sc_wrt_T Sc1 T1 = subst_skvar_Sc T1 beta1 (open_Sc_wrt_T Sc1 (T__Var_f beta1)).
Proof.
unfold open_Sc_wrt_T; default_simp.
Qed.

#[export] Hint Resolve subst_skvar_Sc_intro : lngen.

Lemma subst_skvar_Tm_intro :
forall beta1 t1 T1,
  beta1 `notin` fsk_Tm t1 ->
  open_Tm_wrt_T t1 T1 = subst_skvar_Tm T1 beta1 (open_Tm_wrt_T t1 (T__Var_f beta1)).
Proof.
unfold open_Tm_wrt_T; default_simp.
Qed.

#[export] Hint Resolve subst_skvar_Tm_intro : lngen.

Lemma subst_tvar_Tm_intro :
forall tx1 t1 t2,
  tx1 `notin` ftv_Tm t1 ->
  open_Tm_wrt_Tm t1 t2 = subst_tvar_Tm t2 tx1 (open_Tm_wrt_Tm t1 (t__Var_f tx1)).
Proof.
unfold open_Tm_wrt_Tm; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_Tm_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
