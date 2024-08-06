Set Warnings "-notation-overridden".

Require Import Preamble.

Require Import Defs.ERels.
Require Import Defs.TmTy.
Require Import Defs.Subx.

Require Import Semantics.LogRel.
Require Import Semantics.rhoDef.
Require Import Semantics.gammaDef.

Definition EquivRel (ψ:E) (σ:Sc) (t1 t2:Tm) :=
    ψ ⊢t t1 ▸ σ
  /\ ψ ⊢t t2 ▸ σ
  /\ forall ρ γ, ⦅ρ, γ⦆ ∈ ⦅𝒟, 𝒢⦆ ⟦ψ⟧
    -> ⦅⟦π1 ρ ▹ ⟦π1 γ ▹__x  t1⟧⟧ × ⟦π2 ρ ▹ ⟦π2 γ ▹__x  t2⟧⟧⦆ ∈ ℰ⟦σ⟧ ρ.
Notation  "ψ ⊢t≈ t1 ≈ t2 ▸ σ" := (EquivRel ψ σ t1 t2) (at level 70, format "ψ  ⊢t≈  t1  ≈  t2  ▸  σ" ) : type_scope.

Lemma Equivrel_E_sk_sub : forall ψ1 ψ2 t1 t2 σ,
    ψ1 ⊢t≈ t1 ≈ t2 ▸ σ
  -> E_sk_sub_x_list_eq ψ1 ψ2
  -> ψ2 ⊢t≈ t1 ≈ t2 ▸ σ.
Admitted.
