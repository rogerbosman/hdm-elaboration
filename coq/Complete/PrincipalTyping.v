Set Warnings "-notation-overridden".

Require Import Preamble.

Require Export Defs.DecA.
Require Export Defs.OpenClose.

Require Export Semantics.EquivRel.

Definition Typable (ψ:E) (e:Ex) := (exists a τ t, ψ ⊢d' e ▸ ⟨a⟩ τ ⤳ t).

Axiom Typable_lc : forall ψ e, Typable ψ e -> lc(e).

Definition SubSumpTmEq (ψ:E) (a1:A) (t1:Tm) (τ1:T) (a2:A) (t2:Tm) (τ2:T) :=
  exists t2',
    SubSumpTm' ψ (Λ a1 ⬪ t1) (∀ a1 ⬪ (S__T τ1)) t2' (∀ a2 ⬪ (S__T τ2))
   /\ ψ ⊢t≈ t2' ≈ (Λ a2 ⬪ t2) ▸ (∀ a2 ⬪ (S__T τ2)).
Definition SubSumpTmEq' (ψ:E) (t1:Tm) (σ1:Sc) (t2:Tm) (σ2:Sc) :=
  exists t2',
    SubSumpTm' ψ t1 σ1 t2' σ2
   /\ ψ ⊢t≈ t2' ≈ t2 ▸ σ2.

Definition PrincipalTyping (ψ:E) (e:Ex) (a__p:A) (τ__p:T) (t__p:Tm) :=
    ψ ⊢d' e ▸ ⟨a__p⟩ τ__p ⤳ t__p
  /\ forall a τ t,
    ψ ⊢d' e ▸ ⟨a⟩ τ ⤳ t
  -> SubSumpTmEq ψ a__p t__p τ__p a t τ.
