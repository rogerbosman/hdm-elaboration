Set Warnings "-notation-overridden,-intuition-auto-with-star".

Require Import Preamble.

Require Import Defs.Sub.
Require Import Defs.Lc.

Require Import Semantics.LogRel.
Require Import Semantics.rhoDef.

Lemma logrel_E_skvars_codom_rho_empty : forall ψ ρ,
    ρ ∈ 𝒟⟦ψ⟧
  -> skvars_codom_rho ρ ≡ ∅.
Proof.
  intro ψ. induction ψ. 2:induction a. all:introv [γ IN]; simp' in IN.
  - rho_destr ρ. 2:inverts IN; inverts H. crush.
  - eauto.
  - destr_logrel_val IN. simpl+. rewrite IHa. 2:eauto.
    forwards: WfT_sk • τ1. eauto.
    forwards: WfT_sk • τ2. eauto.
    fsetdec.
  - destr_logrel_val IN. eauto.
  - eauto.
Qed.

Lemma logrel_E_dom_rho_E_A_skvars : forall ψ ρ,
    ρ ∈ 𝒟⟦ψ⟧
  -> dom_rho ρ ≡ E_A_skvars ψ.
Proof.
  intro ψ. induction ψ. 2:induction a. all:introv [γ IN]; simp' in IN.
  - rho_destr ρ. 2:inverts IN; inverts H. crush.
  - simpl+. eauto.
  - destr_logrel_val IN. simpl+. rewrite IHa. 2:eauto.
    simpl+. fsetdec.
  - destr_logrel_val IN. simpl+. eauto.
  - simpl+. eauto.
Qed.

Lemma rho_lc_cons_valid : forall tri α ρ,
    rho_elem_valid tri
  -> lc(ρ)
  -> lc((tri, α) :: ρ).
Proof. intros [[t1 t2] R]. intros. apply rho_lc_cons; eauto. Qed.
