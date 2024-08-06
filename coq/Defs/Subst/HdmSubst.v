Set Warnings "-notation-overridden,-intuition-auto-with-star".

Require Import Preamble.
Require Import Defs.HdmLems.

Require Export Defs.Subst.Notation.

(*** Subst_notin *)
Section subst_var_notin.
  Variable (e:Ex).
  Variable (x:var).

  Fact subst_var_Ex_notin : forall (e':Ex),
      x ∉ fv__x(e')
    -> { e ≔__x x } e' = e'.
  Proof. crush. Qed.
End subst_var_notin.

Section subst_var_notin.
  Variable (t:Tm).
  Variable (tx:tvar).

  Fact subst_tvar_Tm_notin : forall (t':Tm),
      tx ∉ fv__x(t')
    -> { t ≔__x tx } t' = t'.
  Proof. crush. Qed.
End subst_var_notin.

Section subst_skvar_notin.
  Variable (τ:T).
  Variable (α:skvar).

  Fact subst_skvar_T_notin : forall (τ':T),
      α ∉ fv__α(τ')
    -> { τ ≔ α } τ' = τ'.
  Proof. crush. Qed.

  Fact subst_skvar_Sc_notin : forall (σ:Sc),
      α ∉ fv__α(σ)
    -> { τ ≔ α } σ = σ.
  Proof. crush. Qed.

  Fact subst_skvar_Tm_notin : forall (t:Tm),
      α ∉ fv__α(t)
    -> { τ ≔ α } t = t.
  Proof. crush. Qed.
End subst_skvar_notin.


(*** HdmLems alternatives *)
Lemma subst_tvar_Tm_subst_skvar_Tm' : forall x α t τ t__in,
    {({τ ≔ α}t__in) ≔__x x} ({τ ≔ α}t) = {τ ≔ α}({t__in ≔__x x} t).
Proof. intros. induction t0; crush. Qed.

(*** SameVars *)
Lemma subst_skvar_T_subst_skvar_T_samevar : forall α β (τ τ':T),
    β ∉ fv__α(τ)
  -> {τ' ≔ β}({T__Var_f β ≔ α}τ) = {τ' ≔ α}τ.
Proof.
  introv NIFV. induction τ.
  - crush.
  - simpl+. destruct (α0 == α).
    + subst. if_taut.
    + if_dec. simpl+ in NIFV. fsetdec. crush.
  - crush.
  - crush.
  - simpl+ in *.
    rewrite IHτ1. 2:fsetdec.
    rewrite IHτ2. 2:fsetdec.
    crush.
Qed.

Lemma subst_skvar_T_subst_skvar_T_samevar' : forall α β (τ τ':T),
    {T__Var_f β ≔ α}({τ' ≔ α}τ) = {({T__Var_f β ≔ α}τ') ≔ α}τ.
Proof.
  introv. induction τ.
  - crush.
  - simpl+. if_dec. crush. simpl+. if_taut.
  - crush.
  - crush.
  - simpl+ in *. crush.
Qed.

Lemma subst_skvar_Sc_subst_skvar_Sc_samevar : forall α β (τ:T) (σ:Sc),
    β ∉ fv__α(σ)
  -> {τ ≔ β}({T__Var_f β ≔ α}σ) = {τ ≔ α}σ.
Proof.
  introv NIFV. induction σ.
  - simpl+. fequals. simpl+ in NIFV. eauto using subst_skvar_T_subst_skvar_T_samevar.
  - simpl+. fequals. crush.
Qed.

Lemma subst_skvar_Tm_subst_skvar_Tm_samevar : forall α β (τ:T) (t:Tm),
    β ∉ fv__α(t)
  -> {τ ≔ β}({T__Var_f β ≔ α}t) = {τ ≔ α}t.
Proof.
  introv NIFV. induction t0. 1,2,3,4,5:crush. all: simpl+ in NIFV; simpl+.
  - specializes IHt0_1. fsetdec. specializes IHt0_2. fsetdec. crush.
  - specializes IHt0. fsetdec. erewrite subst_skvar_T_subst_skvar_T_samevar. 2:fsetdec. crush.
  - specializes IHt0. fsetdec. erewrite subst_skvar_T_subst_skvar_T_samevar. 2:fsetdec. crush.
  - specializes IHt0. fsetdec. crush.
Qed.

Lemma subst_skvar_Tm_subst_skvar_Tm_samevar' : forall α β (τ:T) (t:Tm),
    {T__Var_f β ≔ α}({τ ≔ α}t) = {({T__Var_f β ≔ α}τ) ≔ α}t.
Proof.
  introv. induction t0. 1,2,3,4,5:crush.
  - simpl+. crush.
  - simpl+. rewrite subst_skvar_T_subst_skvar_T_samevar'. crush.
  - simpl+. rewrite subst_skvar_T_subst_skvar_T_samevar'. crush.
  - simpl+. crush.
Qed.
