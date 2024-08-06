Set Warnings "-notation-overridden,-intuition-auto-with-star".

Require Import Preamble.
Require Import Defs.HdmLems.

Require Import Defs.List.

(* Require Import Defs.Subst. *)
Require Import Defs.Subst.Notation.


(*** Notation *)
Notation lc_Sub θ := (forall (τ:T), TSetI.In τ (codom_Sub θ) -> lc_T τ).
Notation  "lc( x )"  := (lc x) (at level 50, format "lc( x )") : type_scope.
#[export] Instance lcable_Sub : lcable Sub := { lc θ := lc_Sub θ }.

Notation lc_Subx θ := (forall (t:Tm), TmSetI.In t (codom_Subx θ) -> lc_Tm t).
Class lcxable (X : Type) :=  lc__x : X -> Prop .
#[export] Instance lcable_Subx : lcxable Subx := { lc__x θ := lc_Subx θ }.

Fact LcScT : forall τ,
    lc(S__T τ) <-> lc(τ).
Proof. split. intro H. inverts H. crush. constructor. crush. Qed.
Corollary LcScT1 : forall τ, lc(S__T τ) -> lc(τ). apply LcScT. Qed.
Corollary LcScT2 : forall τ, lc_T(τ) -> lc(S__T τ). apply LcScT. Qed.
#[export] Hint Resolve LcScT1 LcScT2 : core.

(*** Help with lcable *)
(* #[export] Hint Extern 5 (lc(_)) => constructor : core. *)

Fact lc_T_tc_rewr : forall τ,
    lc(τ)
  -> lc_T τ.
Proof. crush. Qed.
Fact lc_Tm_tc_rewr : forall t,
    lc(t)
  -> lc_Tm t.
Proof. crush. Qed.
#[export] Hint Resolve lc_T_tc_rewr lc_Tm_tc_rewr : core.

(*** Creating *)
Fact lc_tapp1 : forall t1 t2,
    lc(t__App t1 t2)
  -> lc(t1).
Proof. intros. inverts H. crush. Qed.
Fact lc_tapp2 : forall t1 t2,
    lc(t__App t1 t2)
  -> lc(t2).
Proof. intros. inverts H. crush. Qed.
#[export] Hint Resolve lc_tapp1 lc_tapp2 : core.

(*** Oppen/close *)
Lemma close_Sc_wrt_A_lc : forall σ a,
    lc(σ)
  -> lc(close_Sc_wrt_A σ a).
Proof.
  introv LC. ind_a a. crush. simpl. crush.
Qed.

Lemma close_Tm_wrt_A_lc : forall t a,
    lc(t)
  -> lc(close_Tm_wrt_A t a).
Proof.
  introv LC. ind_a a. crush. simpl. crush.
Qed.

(*** Subst *)
Lemma lc_substskvar_T : forall (τ__in τ:T) α,
    lc(τ__in)
  -> lc(τ)
  -> lc({ τ__in ≔ α }τ).
Proof. intros. crush. Qed.

Lemma lc_substskvar_Tm : forall (t:Tm) (τ:T) α,
    lc(t)
  -> lc(τ)
  -> lc({ τ ≔ α }t).
Proof. intros. crush. Qed.
