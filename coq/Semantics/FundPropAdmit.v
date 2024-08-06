Set Warnings "-notation-overridden,-intuition-auto-with-star".

Require Import Preamble.

Require Import Defs.FrA.
Require Import Defs.OpenClose.
Require Import Defs.TmTy.
Require Import Defs.WfSTt.

Require Import Semantics.EquivRel.

Axiom CompatVar : forall ψ x σ,
    E_lookup ψ x = Some σ
  -> ψ ⊢t≈ (t__Var_f x) ≈ (t__Var_f x) ▸ σ.

Axiom CompatUnit : forall ψ,
    ψ ⊢t≈ t__Unit ≈ t__Unit ▸ S__T T__Unit.

Axiom CompatTrue : forall ψ,
    ψ ⊢t≈ t__True ≈ t__True ▸ S__T T__Bool.

Axiom CompatFalse : forall ψ,
    ψ ⊢t≈ t__False ≈ t__False ▸ S__T T__Bool.

Axiom CompatLam'' : forall ψ t t' τ τ' x,
    ψ ::x x :- S__T τ  ⊢t≈ (open_Tm_wrt_Tm t (t__Var_f x)) ≈ (open_Tm_wrt_Tm t' (t__Var_f x)) ▸ S__T τ'
  -> x ∉ E_names ψ ∪ fv__x(t) ∪ fv__x(t')
  -> ψ ⊢wfτ τ
  -> ψ ⊢t≈ t__Lam τ t ≈ t__Lam τ t' ▸ S__T (T__Fun τ τ').

Axiom CompatLam : forall L ψ t τ t' τ',
    (forall x, x ∉ L -> ψ ::x x :- S__T τ  ⊢t≈ (open_Tm_wrt_Tm t (t__Var_f x)) ≈ (open_Tm_wrt_Tm t' (t__Var_f x)) ▸ S__T τ')
  -> ψ ⊢wfτ τ
  -> ψ ⊢t≈ t__Lam τ t ≈ t__Lam τ t' ▸ S__T (T__Fun τ τ').

Axiom CompatLam' : forall ψ t t' τ τ' x,
    ψ ::x x :- S__T τ  ⊢t≈ (open_Tm_wrt_Tm t (t__Var_f x)) ≈ (open_Tm_wrt_Tm t' (t__Var_f x)) ▸ S__T τ'
  -> x ∉ E_names ψ ∪ fv__x(t) ∪ fv__x(t')
  -> ψ ⊢wfτ τ
  -> ψ ⊢t≈ t__Lam τ t ≈ t__Lam τ t' ▸ S__T (T__Fun τ τ').

Axiom CompatApp : forall ψ t1 t1' t2 t2' τ' τ,
    ψ ⊢t≈ t1 ≈ t2 ▸ S__T (T__Fun τ' τ)
  -> ψ ⊢t≈ t1' ≈ t2' ▸ S__T τ'
  -> ψ ⊢t≈ t__App t1 t1' ≈ t__App t2 t2' ▸ S__T τ.

Axiom CompatTLam : forall L ψ t t' σ,
    (forall α, α ∉ L -> ψ ::a [α] ⊢t≈ (open_Tm_wrt_T t (T__Var_f α)) ≈ (open_Tm_wrt_T t' (T__Var_f α)) ▸ open_Sc_wrt_T σ (T__Var_f α))
  -> ψ ⊢t≈ t__TLam t ≈ t__TLam t' ▸ S__Forall σ.

Axiom CompatTApp : forall ψ t t' σ τ,
    ψ ⊢t≈ t ≈ t' ▸ S__Forall σ
  -> ψ ⊢wfτ τ
  -> ψ ⊢t≈ t__TApp t τ ≈ t__TApp t' τ ▸ open_Sc_wrt_T σ τ.

Axiom CompatTLamA : forall ψ t1 t2 σ a,
    ψ ::a a ⊢t≈ t1 ≈ t2 ▸ σ
  -> a ### (E_skvars ψ ∪ fv__α(σ) ∪ fv__α(t1) ∪ fv__α(t2))
  -> ψ ⊢t≈ (Λ a ⬪ t1) ≈ (Λ a ⬪ t2) ▸ (∀ a ⬪ σ).

Theorem FundamentalProperty : forall ψ t σ,
    ψ  ⊢t t ▸ σ
  -> ψ  ⊢t≈ t ≈ t ▸ σ.
Proof.
  introv TMTY. induction TMTY; eauto using CompatVar, CompatUnit, CompatTrue, CompatFalse, CompatLam, CompatApp, CompatTLam, CompatTApp.
Qed.
