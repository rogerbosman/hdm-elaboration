Set Warnings "-notation-overridden,-intuition-auto-with-star".

Require Import Preamble.
Require Import Defs.HdmLems.

Require Import Defs.ERels.
Require Import Defs.Lc.
Require Import Defs.List.
Require Import Defs.FrA.
Require Import Defs.OpenClose.
Require Import Defs.Sub.
Require Import Defs.Subx.
Require Import Defs.TmTy.

Require Import Semantics.ClosedVals.
Require Import Semantics.gamma.
Require Import Semantics.EquivRel.
Require Import Semantics.LogRel.
Require Import Semantics.LogRelEProps.
Require Import Semantics.logrel_val_props.
Require Import Semantics.Opsem.
Require Import Semantics.rho.

(*** TLam *)
Lemma CompatTLam : forall L ψ t t' σ,
    (forall α, α ∉ L -> ψ ::a [α] ⊢t≈ (open_Tm_wrt_T t (T__Var_f α)) ≈ (open_Tm_wrt_T t' (T__Var_f α)) ▸ open_Sc_wrt_T σ (T__Var_f α))
  -> ψ ⊢t≈ t__TLam t ≈ t__TLam t' ▸ S__Forall σ.
Proof.
  introv IH.
  forwards TMTY1: TmTy__TAbs L. intros. forwards [TmTy [_ _]]: IH H. eassumption.
  forwards TMTY2: TmTy__TAbs L. intros. forwards [_ [TmTy _]]: IH H. eassumption.
  splits. eassumption. eassumption.
  (**)
  introv IN.
  eapply TmTy_close1 in TMTY1. 2:eassumption.
  eapply TmTy_close2 in TMTY2. 2:eassumption.
  simpl+ in TMTY1. simpl+ in TMTY2. simpl+.
  (**)
  apply logrel_val_exp. simp'. splits. splits; simpl+; eauto.
  do 2 eexists. splits. 1,2:reflexivity.
  exists (L ∪ dom_rho ρ ∪ dom_Sub (π1 ρ) ∪ dom_Sub (π2 ρ) ∪ fv__α(⟦π1 ρ ▹ ⟦π1 γ ▹__x t0⟧⟧) ∪ fv__α(⟦π2 ρ ▹ ⟦π2 γ ▹__x t'⟧⟧)).
  intros α NIL__α. introv REL. simpl+ in REL.
  specializes IH α. specializes IH. fsetdec. destruct IH as [TMTY1' [TMTY2' IH]].
  specializes IH ((τ1, τ2, R, α) :: ρ) γ.
  assert (IN': ⦅(τ1, τ2, R, α) :: ρ, γ⦆ ∈ ⦅𝒟, 𝒢⦆⟦ψ ::a [α]⟧). unfold one. simp'.
    do 4 eexists. splits. reflexivity. auto. fsetdec. simp'.
  specializes IH. eassumption.
  destruct IH as [TMTY1'' [TMTY2'' [v1 [v2 [OP1 [OP2 VAL]]]]]]. simpl+ in OP1. simpl+ in OP2.
  splits.
  - forwards: TmTy_close1 ((τ1, τ2, R, α) :: ρ) TMTY1'. eassumption.
    applys_eq H. simpl+.
    rewrite Subx_app_open_Tm_wrt_T. 2:eauto.
    rewrite Sub_app_open_Tm_wrt_T_notindom. 2:eauto. 2:symmetry; simpl+; fsetdec.
    rewrite subst_skvar_Tm_open_Tm_wrt_T. 2:jauto. fequals.
    symmetry. apply subst_skvar_Tm_notin. fsetdec.
    simpl+. if_taut.
  - forwards: TmTy_close2 ((τ1, τ2, R, α) :: ρ) TMTY2'. eassumption.
    applys_eq H. simpl+.
    rewrite Subx_app_open_Tm_wrt_T. 2:eauto.
    rewrite Sub_app_open_Tm_wrt_T_notindom. 2:eauto. 2:symmetry; simpl+; fsetdec.
    rewrite subst_skvar_Tm_open_Tm_wrt_T. 2:jauto. fequals.
    symmetry. apply subst_skvar_Tm_notin. fsetdec.
    simpl+. if_taut.
  - exists v1 v2. splits.
    + applys_eq OP1.
      rewrite Subx_app_open_Tm_wrt_T. 2:eauto.
      rewrite Sub_app_open_Tm_wrt_T_notindom. 2:eauto. 2:symmetry; clear - NIL__α; simpl+; fsetdec.
      rewrite subst_skvar_Tm_open_Tm_wrt_T. simpl+. if_taut.
      rewrite subst_skvar_Tm_notin. reflexivity. fsetdec. jauto.
    + applys_eq OP2.
      rewrite Subx_app_open_Tm_wrt_T. 2:eauto.
      rewrite Sub_app_open_Tm_wrt_T_notindom. 2:eauto. 2:symmetry; clear - NIL__α; simpl+; fsetdec.
      rewrite subst_skvar_Tm_open_Tm_wrt_T. simpl+. if_taut.
      rewrite subst_skvar_Tm_notin. reflexivity. fsetdec. jauto.
    + eassumption.
Qed.

Lemma EquivRelRename : forall α β ψ t1 t2 σ,
    ψ ⊢t≈ t1 ≈ t2 ▸ σ
  -> ({β ↤ α}ψ) ⊢t≈ ({T__Var_f β ≔ α} t1) ≈ ({T__Var_f β ≔ α} t2) ▸ ({T__Var_f β ≔ α} σ).
Admitted.

Lemma CompatTLam' : forall ψ t t' σ α,
    ψ ::a [α] ⊢t≈ (open_Tm_wrt_T t (T__Var_f α)) ≈ (open_Tm_wrt_T t' (T__Var_f α)) ▸ open_Sc_wrt_T σ (T__Var_f α)
  -> α ∉ (E_skvars ψ ∪ fv__α(σ) ∪ fv__α(t) ∪ fv__α(t'))
  -> ψ ⊢t≈ t__TLam t ≈ t__TLam t' ▸ S__Forall σ.
Proof.
  introv EQ NI__α. applys CompatTLam empty. introβ.
  forwards EQ': EquivRelRename α β EQ.
  applys_eq EQ'.
  - simpl+. rewrite rename_skvar_E_notin. 2:fsetdec. crush.
  - rewrite subst_skvar_Sc_open_Sc_wrt_T. 2:crush. simpl+. if_taut.
    subst_notin.
  - rewrite subst_skvar_Tm_open_Tm_wrt_T. 2:crush. simpl+. if_taut.
    subst_notin.
  - rewrite subst_skvar_Tm_open_Tm_wrt_T. 2:crush. simpl+. if_taut.
    subst_notin.
Qed.

(* Lemma CompatTLam'' : forall ψ t t' σ α, *)
(*     ψ ::a [α] ⊢t≈ t ≈ t' ▸ σ *)
(*   -> ψ ⊢t≈ t__TLam (close_Tm_wrt_T α t) ≈ t__TLam (close_Tm_wrt_T α t') ▸ S__Forall (close_Sc_wrt_T α σ). *)
(* Proof. *)
(*   introv [TMTY1 [TMTY2 IH]]. *)
(*   forwards TMTY1': TmTy__TAbs empty. introβ. asserts_rewrite (β = α). admit. applys_eq TMTY1. *)
(*     rewrite open_Tm_wrt_T_close_Tm_wrt_T. reflexivity. *)
(*     rewrite open_Sc_wrt_T_close_Sc_wrt_T. reflexivity. *)
(*   forwards TMTY2': TmTy__TAbs empty. introβ. asserts_rewrite (β = α). admit. applys_eq TMTY2. *)
(*     rewrite open_Tm_wrt_T_close_Tm_wrt_T. reflexivity. *)
(*     rewrite open_Sc_wrt_T_close_Sc_wrt_T. reflexivity. *)
(*   splits. eassumption. eassumption. *)
(*   (**) *)
(*   introv IN. *)
(*   eapply TmTy_close1 in TMTY1'. 2:eassumption. *)
(*   eapply TmTy_close2 in TMTY2'. 2:eassumption. *)
(*   simpl+ in TMTY1'. simpl+ in TMTY2'. simpl+. *)
(*   (**) *)
(*   apply logrel_val_exp. simp'. splits. splits; simpl+; eauto. *)
(*   do 2 eexists. splits. 1,2:reflexivity. *)
(*   exists (dom_rho ρ ∪ dom_Sub (π1 ρ) ∪ dom_Sub (π2 ρ) ∪ fv__α(⟦π1 ρ ▹ ⟦π1 γ ▹__x t0⟧⟧) ∪ fv__α(⟦π2 ρ ▹ ⟦π2 γ ▹__x t'⟧⟧)). *)
(*   intros β NIL__β. introv REL. simpl+ in REL. *)
(*   (* specializes IH α. *) *)
(*   specializes IH ((τ1, τ2, R, α) :: ρ) γ. *)
(*   assert (IN': ⦅(τ1, τ2, R, α) :: ρ, γ⦆ ∈ ⦅𝒟, 𝒢⦆⟦ψ ::a [α]⟧). unfold one. simp'. *)
(*     do 4 eexists. splits. reflexivity. auto. admit. simp'. *)
(*   specializes IH. eassumption. *)
(*   destruct IH as [TMTY1'' [TMTY2'' [v1 [v2 [OP1 [OP2 VAL]]]]]]. simpl+ in OP1. simpl+ in OP2. *)
(*   splits. *)
(*   - forwards: TmTy_close1 ((τ1, τ2, R, α) :: ρ) TMTY1. eassumption. *)
(*     applys_eq H. simpl+. *)
(*     rewrite Subx_app_open_Tm_wrt_T. 2:eauto. *)
(*     rewrite Sub_app_open_Tm_wrt_T_notindom. 2:eauto. 2:symmetry; simpl+; fsetdec. *)
(*     rewrite subst_skvar_Tm_open_Tm_wrt_T. 2:jauto. fequals. *)
(*     symmetry. apply subst_skvar_Tm_notin. fsetdec. *)
(*     simpl+. if_taut. *)
(*   - forwards: TmTy_close2 ((τ1, τ2, R, α) :: ρ) TMTY2'. eassumption. *)
(*     applys_eq H. simpl+. *)
(*     rewrite Subx_app_open_Tm_wrt_T. 2:eauto. *)
(*     rewrite Sub_app_open_Tm_wrt_T_notindom. 2:eauto. 2:symmetry; simpl+; fsetdec. *)
(*     rewrite subst_skvar_Tm_open_Tm_wrt_T. 2:jauto. fequals. *)
(*     symmetry. apply subst_skvar_Tm_notin. fsetdec. *)
(*     simpl+. if_taut. *)
(*   - exists v1 v2. splits. *)
(*     + applys_eq OP1. *)
(*       rewrite Subx_app_open_Tm_wrt_T. 2:eauto. *)
(*       rewrite Sub_app_open_Tm_wrt_T_notindom. 2:eauto. 2:symmetry; clear - NIL__α; simpl+; fsetdec. *)
(*       rewrite subst_skvar_Tm_open_Tm_wrt_T. simpl+. if_taut. *)
(*       rewrite subst_skvar_Tm_notin. reflexivity. fsetdec. jauto. *)
(*     + applys_eq OP2. *)
(*       rewrite Subx_app_open_Tm_wrt_T. 2:eauto. *)
(*       rewrite Sub_app_open_Tm_wrt_T_notindom. 2:eauto. 2:symmetry; clear - NIL__α; simpl+; fsetdec. *)
(*       rewrite subst_skvar_Tm_open_Tm_wrt_T. simpl+. if_taut. *)
(*       rewrite subst_skvar_Tm_notin. reflexivity. fsetdec. jauto. *)
(*     + eassumption. *)
(* Qed. *)

Lemma CompatTLamA : forall ψ t1 t2 σ a,
    ψ ::a a ⊢t≈ t1 ≈ t2 ▸ σ
  -> a ### (E_skvars ψ ∪ fv__α(σ) ∪ fv__α(t1) ∪ fv__α(t2))
  -> ψ ⊢t≈ (Λ a ⬪ t1) ≈ (Λ a ⬪ t2) ▸ (∀ a ⬪ σ).
Proof.
  introv EQ FR. gen ψ. ind_a a; intros.
  - simpl+. simpl+ in EQ.
    eapply Equivrel_E_sk_sub. eassumption. split; reldec.
  - specializes IHa (ψ ::a [α]).
    specializes IHa. eapply Equivrel_E_sk_sub. eassumption. split; reldec.
    eapply FrA_shift in FR. FrA_L_sub.
    simpl+. applys_eq CompatTLam'. applys_eq IHa.
    + apply open_Sc_wrt_T_close_Sc_wrt_T.
    + apply open_Tm_wrt_T_close_Tm_wrt_T.
    + apply open_Tm_wrt_T_close_Tm_wrt_T.
    + rewrite fsk_Sc_close_Sc_wrt_T. rewrite fsk_close_Sc_wrt_A.
      rewrite fsk_Tm_close_Tm_wrt_T. rewrite fsk_close_Tm_wrt_A.
      rewrite fsk_Tm_close_Tm_wrt_T. rewrite fsk_close_Tm_wrt_A.
      eapply FrA_cons2 in FR. fsetdec.
Qed.
