Set Warnings "-notation-overridden,-intuition-auto-with-star".

Require Import Preamble.

Require Import Defs.Lc.
Require Import Defs.Sub.

Require Export Semantics.Projable.

(*** Def *)

Definition 𝓡 := relation Tm.

Definition rho_elem := (T * T * 𝓡).

Definition rho_elem_proj1 : rho_elem -> T := fst ∘ fst.
Definition rho_elem_proj2 : rho_elem -> T := snd ∘ fst.
Definition rho_elem_proj__R : rho_elem -> 𝓡 := snd.

Definition rho := list (rho_elem * skvar).

Ltac ind_rho ρ := induction ρ as [|[[[?τ1 ?τ2] ?R] ?α]].
Ltac rho_destr ρ := destruct ρ as [|[[[?τ1 ?τ2] ?R] ?α] ρ].

Definition map_snd [A B C:Type] (f:A -> B) : list (A*C) -> list (B*C) :=
  map (fun (p:(A*C)) => let (x, y) := p in (f x, y)).

Definition rho_proj1 : rho -> Sub := map_snd rho_elem_proj1.
Definition rho_proj2 : rho -> Sub := map_snd rho_elem_proj2.
#[derive(equations=no)] Equations rho_proj__R (ρ:rho) (α:skvar) : option 𝓡 :=
  rho_proj__R [] _ := None;
  rho_proj__R ((tri, β)::ρ') α := if eq_skvar α β then Some (rho_elem_proj__R tri) else rho_proj__R ρ' α.

(*** Projable *)
#[export] Instance rho_proj1able : proj1able rho Sub := { π1 := rho_proj1 }.
#[export] Instance rho_proj2able : proj2able rho Sub := { π2 := rho_proj2 }.
#[export] Instance rho_projRable : projRable rho skvar (option 𝓡) := { π__R := rho_proj__R }.

Lemma π1_rho_app_distr : forall ρ1 ρ2,
    π1 (ρ1 ++ ρ2) = π1 ρ1 ++ π1 ρ2.
Proof. intros. ind_rho ρ1. crush. simpl+. crush. Qed.
Lemma π2_rho_app_distr : forall ρ1 ρ2,
    π2 (ρ1 ++ ρ2) = π2 ρ1 ++ π2 ρ2.
Proof. intros. ind_rho ρ1. crush. simpl+. crush. Qed.
#[export] Hint Rewrite π1_rho_app_distr π2_rho_app_distr : sub_dist.

Definition dom_rhodom_list : rho -> list skvar := map snd.

(*** dom_rho *)
Module dom_rho_alg <: List_to_Set_alg TaggedAtom AtomSetImpl.
  Definition elt := (rho_elem * atom)%type.
  Definition f : elt -> atoms := (AtomSetImpl.singleton ∘ snd).
End dom_rho_alg.
#[export] Hint Unfold dom_rho_alg.elt dom_rho_alg.f : algs.
Module Export dom_rho := List_to_Set TaggedAtom AtomSetImpl dom_rho_alg.
Notation dom_rho := dom_rho.List_to_Set.

Fact proj1_dom_rho_Sub : forall ρ, dom_Sub (π1 ρ) ≡ dom_rho ρ.
Proof. intros. ind_rho ρ; simpl+; crush. Qed.
Fact proj2_dom_rho_Sub : forall ρ, dom_Sub (π2 ρ) ≡ dom_rho ρ.
Proof. intros. ind_rho ρ; simpl+; crush. Qed.

Fact proj1_rho_dom_Sub_hint : forall α ρ,
    α ∉ dom_rho ρ
  -> α ∉ dom_Sub (π1 ρ).
Proof. intros. rewrite proj1_dom_rho_Sub. crush. Qed.
Fact proj2_rho_dom_Sub_hint : forall α ρ,
    α ∉ dom_rho ρ
  -> α ∉ dom_Sub (π2 ρ).
Proof. intros. rewrite proj2_dom_rho_Sub. crush. Qed.
#[export] Hint Resolve proj1_rho_dom_Sub_hint proj2_rho_dom_Sub_hint  : core.

Lemma proj12_dom_rho_Sub : forall γ,
    dom_rho γ ≡ dom_Sub (π1 γ) ∪ dom_Sub (π2 γ).
Proof. intros. rewrite proj1_dom_rho_Sub. rewrite proj2_dom_rho_Sub. fsetdec. Qed.
#[export] Hint Rewrite proj12_dom_rho_Sub : logrel_E_rho.
Ltac split_rho := autorewrite with logrel_E_rho in *.

(*** codom_rho *)
Module skvars_codom_rho_alg <: List_to_Set_alg TaggedAtom AtomSetImpl.
  Definition elt := (rho_elem * skvar)%type.
  Definition f : elt -> atoms := fun elt => (fsk ∘ fst ∘ fst ∘ fst) elt ∪ (fsk ∘ snd ∘ fst ∘ fst) elt.
End skvars_codom_rho_alg.
#[export] Hint Unfold skvars_codom_rho_alg.elt skvars_codom_rho_alg.f : algs.

Module Export Skvars_codom_rho := List_to_Set TaggedAtom AtomSetImpl skvars_codom_rho_alg.
Notation skvars_codom_rho := Skvars_codom_rho.List_to_Set.

Lemma proj1_skvars_codom_rho_Sub : forall ρ, skvars_codom_Sub (π1 ρ) ⊆ skvars_codom_rho ρ.
Proof. intros. ind_rho ρ. crush. simpl+. fsetdec. Qed.
Lemma proj2_skvars_codom_rho_Sub : forall ρ, skvars_codom_Sub (π2 ρ) ⊆ skvars_codom_rho ρ.
Proof. intros. ind_rho ρ. crush. simpl+. fsetdec. Qed.

Fact proj1_skvars_codom_rho_Sub_hint : forall α ρ,
    α ∉ skvars_codom_rho ρ
  -> α ∉ skvars_codom_Sub (π1 ρ).
Proof. intros. rewrite proj1_skvars_codom_rho_Sub. crush. Qed.
Fact proj2_skvars_codom_rho_Sub_hint : forall α ρ,
    α ∉ skvars_codom_rho ρ
  -> α ∉ skvars_codom_Sub (π2 ρ).
Proof. intros. rewrite proj2_skvars_codom_rho_Sub. crush. Qed.
#[export] Hint Resolve proj1_skvars_codom_rho_Sub_hint proj2_skvars_codom_rho_Sub_hint  : core.



(*** Lc *)
Definition lc_rho (ρ:rho) : Prop := lc(π1 ρ) /\ lc(π2 ρ).
#[export] Instance lcable_rho : lcable rho := { lc := lc_rho }.

Fact lc_rho_empty :
    lc([]:rho).
Proof. do 3 unfolds. simpl+. crush. Qed.
#[export] Hint Resolve lc_rho_empty : core.

Fact lc_ρ_π1 : forall ρ,
    lc(ρ)
  -> lc(π1 ρ).
Proof. crush. Qed.
Fact lc_ρ_π2 : forall ρ,
    lc(ρ)
  -> lc(π2 ρ).
Proof. crush. Qed.
#[export] Hint Resolve lc_ρ_π1 lc_ρ_π2 : core.

Lemma rho_lc_cons : forall τ1 τ2 R a ρ,
    lc(τ1)
  -> lc(τ2)
  -> lc(ρ)
  -> lc ((τ1, τ2, R, a) :: ρ).
Proof. intros. split; simpl+; apply lc_Sub_cons; eauto. Qed.

Lemma cons_rho_lc : forall τ1 τ2 R a ρ,
    lc ((τ1, τ2, R, a) :: ρ)
  -> lc(τ1)
  /\ lc(τ2)
  /\ lc(ρ).
Proof. introv [LC1 LC2]. simpl+ in *. splits; eauto. split; eauto. Qed.
