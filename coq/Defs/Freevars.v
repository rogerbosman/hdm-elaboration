Set Warnings "-notation-overridden,-intuition-auto-with-star".

Require Import Preamble.
Require Import Defs.HdmLems.

Require Import Defs.List.
Require Import Defs.Subst.Notation.

(*** Notation *)
(** Free vars *)

(** Free skvars *)

(*** Simplification *)
Fact free_skvars_T_Fun : forall τ1 τ2,
    fv__α(T__Fun τ1 τ2) = fv__α(τ1) ∪ fv__α(τ2).
Proof. reflexivity. Qed.
#[export] Hint Rewrite free_skvars_T_Fun : core.

Fact fsk_S__Forall : forall σ,
  fv__α(S__Forall σ) = fv__α(σ).
Proof. crush. Qed.

Lemma fsk_Tm_subst_tvar_Tm_no_sk : forall x__in x__out t,
    fv__α({t__Var_f x__in ≔__x x__out}t) ≡ fv__α(t).
Proof. intros. induction t0; simpl+; crush. Qed.
#[export] Hint Rewrite fsk_Tm_subst_tvar_Tm_no_sk : core.

Lemma ftv_Tm_subst_skvar_Tm_eq : forall (τ:T) α (t:Tm),
    fv__x({τ ≔ α}t) ≡ fv__x(t).
Proof. intros. induction t0; crush. Qed.

(*** Open/close *)
Lemma fsk_close_Sc_wrt_A : forall σ a,
    fv__α(close_Sc_wrt_A σ a) ≡ fv__α(σ) ∖ varl a.
Proof.
  intros. ind_a a. fsetdec. simpl+. remember (close_Sc_wrt_A σ a) as σ'.
  rewrite fsk_Sc_close_Sc_wrt_T. fsetdec.
Qed.

Lemma fsk_close_Tm_wrt_A : forall t a,
    fv__α(close_Tm_wrt_A t a) ≡ fv__α(t) ∖ varl a.
Proof.
  intros. ind_a a. fsetdec. simpl+. remember (close_Tm_wrt_A t0 a) as t'.
  rewrite fsk_Tm_close_Tm_wrt_T. fsetdec.
Qed.

Fact ftv_close_Tm_wrt_A : forall t a,
    fv__x(close_Tm_wrt_A t a) ≡ fv__x(t).
Proof. introv. ind_a a. crush. simpl+. rewrite <- IHa. crush. Qed.
#[export] Hint Rewrite ftv_close_Tm_wrt_A : core.

