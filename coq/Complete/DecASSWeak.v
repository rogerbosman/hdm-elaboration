Set Warnings "-notation-overridden,-intuition-auto-with-star".

Require Import Preamble.
(* Require Import Defs.HdmLems. *)

Require Import Defs.E.
(* Require Import Defs.ERels. *)
(* Require Import Defs.List. *)
(* Require Import Defs.FrA. *)
Require Import Defs.Foralls.
Require Import Defs.OpenClose.
(* Require Import Defs.Sub. *)
(* Require Import Defs.Subst. *)
Require Import Defs.TmTy.
(* Require Import Defs.Rename. *)
Require Import Defs.WfSTt.

Require Import Defs.DecA.

Require Import Semantics.EquivRel.


(*** SSA rewr *)
Require Import Defs.ERels.
Require Import Defs.FrA.
Notation E_sk_sub := M_E_skvars.R__sub.
#[export] Hint Unfold E_sk_sub : defs rels.

Notation E_A_sk_sub := M_E_A_skvars.R__sub.
#[export] Hint Unfold E_sk_sub : defs rels.

Lemma SubSumpTmA_E_A_sk_sub : forall ψ1 ψ2 t1 σ t2 τ a,
    SubSumpTmA ψ1 t1 σ t2 a τ
  -> E_sk_sub ψ2 ψ1
  -> E_A_sk_sub ψ1 ψ2
  -> SubSumpTmA ψ2 t1 σ t2 a τ.
Proof.
  introv SSA. gen ψ2. induction SSA; introv EQ1 EQ2; unfolds in EQ1; unfolds in EQ2.
  - econstructor. applys FrA_L_sub FR. eassumption.
  - econstructor. applys FrA_L_sub FR. eassumption.
    applys WfT_E_A_sk_sub WFT. erel_fsetdec.
    applys IHSSA. erel_fsetdec. erel_fsetdec.
Qed.

Lemma SSA_weaken_binding : forall σ2 σ1 ψ t1 t2 x a τ t,
    SubSumpTm' ψ t1 σ1 t2 σ2
  -> SubSumpTmA ψ (t__Var_f x) σ2 (open_Tm_wrt_Tm t  (t__Var_f x)) a τ
  -> ψ ⊢t t2 ▸ σ2
  -> ψ ⊢t t1 ▸ σ1
  -> exists t' a' τ',
      SubSumpTmA ψ (t__Var_f x) σ1 (open_Tm_wrt_Tm t' (t__Var_f x)) a' τ'
   /\ (∀ a' ⬪ S__T τ') = (∀ a ⬪ S__T τ)
  /\ ψ ⊢t≈ (Λ a'⬪ (open_Tm_wrt_Tm t' t1)) ≈ (Λ a⬪ (open_Tm_wrt_Tm t t2)) ▸ (S__T τ).
Admitted.

Theorem DecA_weaken_binding : forall σ1 ψ1 x σ2 ψ2 e a τ t t2 t1,
    ((ψ1 ::x x :- σ2) +++ ψ2) ⊢d' e ▸ ⟨a⟩ τ ⤳ (open_Tm_wrt_Tm t (t__Var_f x))
  -> ψ1 ⊢t t2  ▸ σ2
  -> ψ1 ⊢t t1 ▸ σ1
  -> SubSumpTm' ψ1 t1 σ1 t2 σ2
  -> exists a' τ' t',
      ((ψ1 ::x x :- σ1) +++ ψ2) ⊢d' e ▸ ⟨a'⟩ τ' ⤳ (open_Tm_wrt_Tm t' (t__Var_f x))
    /\ (∀ a'⬪ S__T τ') = (∀ a⬪ S__T τ)
    /\ ψ1 ⊢t≈ (Λ a'⬪ (open_Tm_wrt_Tm t' t1)) ≈ (Λ a⬪ (open_Tm_wrt_Tm t t2)) ▸ (S__T τ).
Proof.
  introv DECA TMTY2 TMTY1 SS. forwards E: DecA_lc. eassumption.
  gen σ1 ψ1 x σ2 ψ2 a τ t0 t2 t1. induction E; intros; inverts DECA.

  - asserts_rewrite (ψ2 = •) in *. admit. simpl+ in *. rename ψ1 into ψ.
    if_dec. 2:admit. symmetry in IN. inverts IN.

    forwards [t' [a' [τ' [SSA [EQ__T EQ__t]]]]]: SSA_weaken_binding ψ. eassumption.
      eapply SubSumpTmA_E_A_sk_sub. eassumption. reldec. reldec. eassumption. eassumption.
    (**)
    exists. splits.
    + econstructor. simpl+. if_taut. reflexivity.
      eapply SubSumpTmA_E_A_sk_sub. eassumption. unfolds. simpl+.
      forwards: WfS_sk σ1. eapply TmTy_WfS. eassumption. admit.
      rewrite E_A_skvars_E_skvars in H. fsetdec. reldec.
    + eassumption.
    + eassumption.
Admitted.
