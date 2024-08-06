Set Warnings "-notation-overridden,-intuition-auto-with-star".

Require Import Preamble.

Require Import Defs.TmTy.
Require Import Defs.Sub.

Require Import Semantics.Opsem.
Require Import Semantics.rhoDef.

(* From Equations Require Import Equations. *)

Definition closed_vals σ (ρ:rho) v1 v2 := (is_val v1 /\ is_val v2 /\ • ⊢t v1 ▸ ⟦π1 ρ ▹ σ⟧ /\ • ⊢t v2 ▸ ⟦π2 ρ ▹ σ⟧).
Corollary closed_vals_v1 : forall (σ:Sc) (ρ:rho) (v1 v2:Tm),
    closed_vals σ ρ v1 v2
  -> is_val v1.
Proof. unfold closed_vals. crush. Qed.
Corollary closed_vals_v2 : forall (σ:Sc) (ρ:rho) (v1 v2:Tm),
    closed_vals σ ρ v1 v2
  -> is_val v2.
Proof. unfold closed_vals. crush. Qed.
Corollary closed_vals_tmty1 : forall (σ:Sc) (ρ:rho) (v1 v2:Tm),
    closed_vals σ ρ v1 v2
  -> • ⊢t v1 ▸ ⟦π1 ρ ▹ σ⟧.
Proof. unfold closed_vals. crush. Qed.
Corollary closed_vals_tmty2 : forall (σ:Sc) (ρ:rho) (v1 v2:Tm),
    closed_vals σ ρ v1 v2
  -> • ⊢t v2 ▸ ⟦π2 ρ ▹ σ⟧.
Proof. unfold closed_vals. crush. Qed.
#[export] Hint Resolve closed_vals_v1 closed_vals_v2 closed_vals_tmty1 closed_vals_tmty2 : core.

Lemma closed_vals_Unit : forall ρ,
    closed_vals (S__T T__Unit) ρ t__Unit t__Unit.
Proof. intros. splits; simpl+; crush. Qed.
Lemma closed_vals_True : forall ρ,
    closed_vals (S__T T__Bool) ρ t__True t__True.
Proof. intros. splits; simpl+; crush. Qed.
Lemma closed_vals_False : forall ρ,
    closed_vals (S__T T__Bool) ρ t__False t__False.
Proof. intros. splits; simpl+; crush. Qed.
#[export] Hint Resolve closed_vals_Unit closed_vals_True closed_vals_False : core.
