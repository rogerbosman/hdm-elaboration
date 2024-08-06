Set Warnings "-notation-overridden,-intuition-auto-with-star".

Require Import Preamble.

Require Import Defs.Lc.
Require Import Defs.Subx.

Require Export Semantics.Projable.


Definition gamma := list ((Tm * Tm) * var).

Ltac ind_gamma γ := induction γ as [|[[τ1 τ2]α] γ].

Definition gamma_proj1 : gamma -> Subx :=
  map (fun p => (fst (fst p), snd p)).
Definition gamma_proj2 : gamma -> Subx :=
  map (fun p => (snd (fst p), snd p)).


#[export] Instance gamma_proj1able : proj1able gamma Subx := { π1 := gamma_proj1 }.
#[export] Instance gamma_proj2able : proj2able gamma Subx := { π2 := gamma_proj2 }.

Module dom_gamma_alg <: List_to_Set_alg TaggedAtom AtomSetImpl.
  Definition elt := ((Tm * Tm) * atom)%type.
  Definition f : elt -> atoms := (AtomSetImpl.singleton ∘ snd).
End dom_gamma_alg.
#[export] Hint Unfold dom_gamma_alg.elt dom_gamma_alg.f : algs.
Module Export dom_gamma := List_to_Set TaggedAtom AtomSetImpl dom_gamma_alg.
Notation dom_gamma := dom_gamma.List_to_Set.

Fact proj1_dom_gamma_Sub : forall γ, dom_Subx (π1 γ) ≡ dom_gamma γ.
Proof. intros. ind_gamma γ; simpl+; crush. Qed.
Fact proj2_dom_gamma_Sub : forall γ, dom_Subx (π2 γ) ≡ dom_gamma γ.
Proof. intros. ind_gamma γ; simpl+; crush. Qed.

Lemma proj12_dom_gamma_Sub : forall γ,
    dom_gamma γ ≡ dom_Subx (π1 γ) ∪ dom_Subx (π2 γ).
Proof. intros. rewrite proj1_dom_gamma_Sub. rewrite proj2_dom_gamma_Sub. fsetdec. Qed.
#[export] Hint Rewrite proj12_dom_gamma_Sub : logrel_E_gam.
Ltac split_gam := autorewrite with logrel_E_gam in *.

(*** Lc *)
Definition lc_gamma (γ:gamma) : Prop := lc__x(π1 γ) /\ lc__x(π2 γ).
#[export] Instance lcable_gamma : lcable gamma := { lc := lc_gamma }.

Fact lc_gamma_empty :
    lc([]:gamma).
Proof. do 3 unfolds. simpl+. crush. Qed.
#[export] Hint Resolve lc_gamma_empty : core.

Fact lcx_γ_π1 : forall (γ:gamma),
    lc(γ)
  -> lc__x(π1 γ).
Proof. crush. Qed.
Fact lcx_γ_π2 : forall (γ:gamma),
    lc(γ)
  -> lc__x(π2 γ).
Proof. crush. Qed.
#[export] Hint Resolve lcx_γ_π1 lcx_γ_π2 : core.

Lemma gamma_lc_cons : forall v1 v2 x (γ:gamma),
    lc(v1)
  -> lc(v2)
  -> lc(γ)
  -> lc (((v1, v2, x) :: γ)).
Proof.
  introv LC__v1 LC__v2 [LC1 LC2].
  split; simpl+; do 2 unfolds; introv IN; simpl+ in IN; destr_union; eauto.
Qed.
