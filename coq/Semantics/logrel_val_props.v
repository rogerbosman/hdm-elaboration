Set Warnings "-notation-overridden,-intuition-auto-with-star".

Require Import Preamble.
Require Import Defs.HdmLems.

(* Require Import Defs.E. *)
(* Require Import Defs.ELookup. *)
(* Require Import Defs.ERels. *)
Require Import Defs.Foralls.
(* Require Import Defs.List. *)
Require Import Defs.TmTy.
(* Require Import Defs.WfSTt. *)
Require Import Defs.Sub.
Require Import Defs.Subx.

Require Import Semantics.ClosedVals.
Require Import Semantics.gammaDef.
Require Import Semantics.LogRel.
(* Require Import Semantics.Opsem. *)
Require Import Semantics.rho.

(* From Equations Require Import Equations. *)


(*** Weakening *)
Lemma fsk_Sub_app_Sc_notindom : forall θ (σ:Sc) α,
    α ∉ dom_Sub θ
  -> α ∈ fv__α(⟦θ ▹ σ⟧)
  -> α ∈ fv__α(σ).
Proof.
  introv NI IN. ind_Sub θ. crush.
  simpl+ in *. apply IHθ. fsetdec.
  dist in IN. destruct (α0 == α). fsetdec.
  rewrite fsk_Sc_subst_skvar_Sc_upper in IN. simpl+ in IN.
  (* is gewoon niet waar, θ kan β ∈ σ bevatten die weer α bevat. *)
Admitted.

Lemma closed_vals_weakening : forall α σ τ1 τ2 R ρ v1 v2,
    α ∉ (dom_rho ρ ∪ fv__α(σ))
  -> closed_vals σ                   ρ  v1 v2
  <-> closed_vals σ ((τ1, τ2, R, α) :: ρ) v1 v2.
Proof.
  introv NICD. split; introv [VAL1 [VAL2 [TMTY1 TMTY2]]]; simpl+ in *; splits; try assumption.
  - applys_eq TMTY1. dist. subst_notin'. intro IN. apply fsk_Sub_app_Sc_notindom in IN. fsetdec.
    rewrite proj1_dom_rho_Sub. fsetdec.
  - applys_eq TMTY2. dist. subst_notin'. intro IN. apply fsk_Sub_app_Sc_notindom in IN. fsetdec.
    rewrite proj2_dom_rho_Sub. fsetdec.
  - applys_eq TMTY1. dist. subst_notin'. intro IN. apply fsk_Sub_app_Sc_notindom in IN. fsetdec.
    rewrite proj1_dom_rho_Sub. fsetdec.
  - applys_eq TMTY2. dist. subst_notin'. intro IN. apply fsk_Sub_app_Sc_notindom in IN. fsetdec.
    rewrite proj2_dom_rho_Sub. fsetdec.
Qed.

Lemma logrel_val_weakening_gammalookup : forall σ ψ α γ τ1 τ2 R ρ v1 v2,
    ⦅ρ, γ⦆ ∈ ⦅𝒟, 𝒢⦆⟦ψ⟧
  -> α ∉ dom_rho ρ
  -> α ∉ fv__α(σ)
  -> ⦅v1 × v2⦆ ∈ 𝒱⟦σ⟧ ρ
  <-> ⦅v1 × v2⦆ ∈ 𝒱⟦σ⟧ (τ1, τ2, R, α) :: ρ.
Proof.
  intro σ. forall_ind σ. induction τ.

  (* all:introv IN VAL; simp' in *; destruct VAL as [CV VAL]; split; try eauto using closed_vals_weakening. *)
  (* - simpl+. if_dec. 2:crush. destruct CV. *)
  (*   forwards: closed_Sc ⟦π1 ρ ▹ S__T (T__Var_f α0)⟧. eapply TmTy_WfS_closed. jauto. simpl+ in H2. *)
  (*   forwards: Sub_app_T_fsk_eq (π1 ρ) (T__Var_f α0) α0. simpl+. fsetdec. destruct H3. fsetdec. *)
  (*   rewrite proj1_dom_rho_Sub in H3. fsetdec. *)
  (* - destruct CV as [_ [_ [TMTY1 TMTY2]]]. simpl+ in TMTY1. simpl+ in TMTY2. *)
  (*   destruct VAL as [t1 [t2 [EQ1 [EQ2 VAL]]]]. subst. exists t1 t2. splits. *)
  (*   forwards: closed_Sc. eapply TmTy_WfS_closed. apply TMTY1. simpl+ in H0. *)
  (*   simpl+. dist. subst_notin. *)
  (*   forwards: closed_Sc. eapply TmTy_WfS_closed. apply TMTY2. simpl+ in H0. *)
  (*   simpl+. dist. subst_notin. *)
  (*   intros v1 v2 VAL. *)
Admitted.


Axiom logrel_val_weakening_compositionality:
(** control over freshness β *)
forall (τ : T) (ρ : list dom_rho_alg.elt) (τ1 τ2 : T) (R : 𝓡) (β : atom) (v1 v2 : Tm), ⦅v1 × v2⦆ ∈ 𝒱⟦S__T τ⟧ ρ <-> ⦅v1 × v2⦆ ∈ 𝒱⟦S__T τ⟧ (τ1, τ2, R, β) :: ρ.


Axiom closed_vals_weakening_compositionality : forall α β tri ρ v1 v2,
    β ∉ (fv__α(⟦π1 ρ ▹ T__Var_f α⟧) ∪ fv__α(⟦π2 ρ ▹ T__Var_f α⟧))
  -> closed_vals (S__T (T__Var_f α)) ((tri, β) :: ρ) v1 v2
  <-> closed_vals (S__T (T__Var_f α)) (           ρ) v1 v2.

(*** Lemmas *)
Fact Sub_app_Sc_fsk_eq : forall (θ:Sub) (τ:Sc) α,
    α ∈ fv__α(τ)
  -> α ∈ fv__α(⟦θ ▹ τ⟧) \/ α ∈ dom_Sub θ.
Proof.
  introv IN. ind_Sub θ. simpl+. crush. destruct (α0 == α).
  - subst. simpl+. right. fsetdec.
  - destruct IHθ; simpl+. 2:right; fsetdec. left. dist.
    rewrite <- fsk_Sc_subst_skvar_Sc_lower. fsetdec.
Qed.

Require Import Defs.List.
Lemma E_lookup_logrel_val : forall ψ γ x σ ρ,
    E_lookup ψ x = Some σ
  -> ⦅ρ, γ⦆ ∈ ⦅𝒟, 𝒢⦆ ⟦ψ⟧
  -> exists v1 v2,
      ⟦π1 γ ▹__x (t__Var_f x)⟧ = v1
    /\ ⟦π2 γ ▹__x (t__Var_f x)⟧ = v2
    /\ ⦅v1 × v2⦆ ∈ 𝒱⟦σ⟧ ρ.
Proof.
  intro ψ. induction ψ. 2:ind_a a. all:introv LU IN.
  - crush.
  - simp' in IN.
  - simp' in IN; destr_logrel_val IN.
    forwards [v1 [v2 [TMTY1 [TMTY2 VAL]]]]: IHa. eassumption. eassumption.
    exists v1 v2. splits. 1,2:assumption.
    assert (α ∉ fv__α(σ)). apply props_logrel_val in VAL. unfolds in VAL. intro IN'.
    eapply (Sub_app_Sc_fsk_eq (π1 ρ')) in IN'. rewrite closed_Sc in IN'. 2:eauto. rewrite proj1_dom_rho_Sub in IN'. fsetdec.
    eauto using logrel_val_weakening_gammalookup. admit.
  - simp' in IN; destr_logrel_val IN. simpl+ in NID. split_gam.
    simpl+ in LU. if_dec.
    + inverts LU. exists v1 v2. splits; simpl+.
      * Subx_notin'. 2:simpl+; fsetdec. simpl+. if_taut.
      * Subx_notin'. 2:simpl+; fsetdec. simpl+. if_taut.
      * assumption.
    + forwards [v1' [v2' [EQ1 [EQ2 VAL']]]]: IHψ. eassumption. eassumption.
      exists v1' v2'. splits.
      * dist. rewrite EQ1. subst_notin'. eauto.
      * dist. rewrite EQ2. subst_notin'. eauto.
      * assumption.
  - simp' in IN.
Admitted.

(*** Move to Sub *)
(* Lemma Sub_app_Sc_notinfv_codom : forall α θ (σ:Sc) τ1, *)
(*     α ∉ skvars_codom_Sub θ ∪ fv__α(σ) *)
(*   -> {τ1 ≔ α}⟦θ ▹ σ⟧ = ⟦θ ▹ σ⟧. *)
(* Proof. intros. subst_notin'. rewrite Sub_app_Sc_fsk'. fsetdec. Qed. *)
(* Lemma Sub_app_T_notinfv_codom : forall α θ (τ:T) τ1, *)
(*     α ∉ skvars_codom_Sub θ ∪ fv__α(τ) *)
(*   -> {τ1 ≔ α}⟦θ ▹ τ⟧ = ⟦θ ▹ τ⟧. *)
(* Proof. intros. subst_notin'. rewrite Sub_app_T_fsk'. fsetdec. Qed. *)

(*** Move to Wft *)
Lemma WfS_fsk_closed : forall t σ,
    • ⊢t t ▸ σ
  -> forall α, α ∉ fv__α(σ).
Proof. intros. rewrite (WfS_sk •); eauto. Qed.
#[export] Hint Resolve WfS_fsk_closed : core.

(* (*** Move to closed_vals *) *)
(* Lemma closed_vals_weakening : forall α σ τ1 τ2 R ρ v1 v2, *)
(*     (* α ∉ (skvars_codom_rho ρ ∪ fv__α(σ)) *) *)
(*   (* -> *) *)
(*     closed_vals σ                   ρ  v1 v2 *)
(*   <-> closed_vals σ ((τ1, τ2, R, α) :: ρ) v1 v2. *)
(* Proof. *)
(*   introv (* NICD *). split; introv [VAL1 [VAL2 [TMTY1 TMTY2]]]; simpl+ in *; splits; try assumption. *)
(*   - dist. subst_notin'. assumption. eauto. *)
(*   - dist. subst_notin'. assumption. eauto. *)
(*   -  *)
(*       . *)
(*     rewrite Sub_app_Sc_notinfv_codom. eassumption. *)
(*     rewrite proj2_skvars_codom_rho_Sub. eassumption. *)
(*   - dist in TMTY1. rewrite Sub_app_Sc_notinfv_codom in TMTY1. eassumption. *)
(*     rewrite proj1_skvars_codom_rho_Sub. eassumption. *)
(*   - dist in TMTY2. rewrite Sub_app_Sc_notinfv_codom in TMTY2. eassumption. *)
(*     rewrite proj2_skvars_codom_rho_Sub. eassumption. *)
(* Qed. *)


(* (*** Move to foralls *) *)
(* Lemma calc_foralls : forall σ, *)
(*     exists n, n = foralls σ. *)
(* Proof. induction σ; eexists; crush. Qed. *)

(* Ltac forall_ind σ := *)
(*   let n := fresh "n" in *)
(*   forwards [n H]: calc_foralls σ; gen σ; induction n; *)
(*     [ intros σ__τ H__foralls; destruct σ__τ; [clear H__foralls | inverts H__foralls] *)
(*     | intros σ__Forall H__foralls; destruct σ__Forall; simpl+ in H__foralls; inverts H__foralls]. *)

(* (*** actual thm *) *)
(* Lemma logrel_val_weakening : forall σ v1 v2 τ1 τ2 R α ρ, *)
(*     ⦅v1 × v2⦆ ∈ 𝒱⟦σ⟧ ρ *)
(*   <-> ⦅v1 × v2⦆ ∈ 𝒱⟦σ⟧ ((τ1, τ2, R, α) :: ρ). *)
(* Proof. *)
(*   intro σ. forall_ind σ. *)
(*   induction τ; introv (* NI *). *)
(*   - split; introv VAL; simp' in VAL; crush. *)
(*   - split; introv VAL; simp' in VAL. *)
(*     + destructs VAL. simp'. split. apply closed_vals_weakening. assumption. assumption. *)
(*       simpl+. if_dec. *)
(*       * simpl+ in NI. fsetdec. *)
(*       * crush. *)
(*     + destructs VAL. simp'. split. apply closed_vals_weakening in H. assumption. assumption. *)
(*       simpl+ in H0. if_dec. *)
(*       * simpl+ in NI. fsetdec. *)
(*       * crush. *)


(* Lemma logrel_val_weakening : forall σ v1 v2 τ1 τ2 R α ρ, *)
(*     α ∉ (skvars_codom_rho ρ ∪ (fv__α(σ) ∖ dom_rho ρ)) *)
(*   -> ⦅v1 × v2⦆ ∈ 𝒱⟦σ⟧ ρ *)
(*   <-> ⦅v1 × v2⦆ ∈ 𝒱⟦σ⟧ ((τ1, τ2, R, α) :: ρ). *)
(* Proof. *)
(*   intro σ. forall_ind σ. *)
(*   induction τ; introv NI. *)
(*   - split; introv VAL; simp' in VAL; crush. *)
(*   - split; introv VAL; simp' in VAL. *)
(*     + destructs VAL. simp'. split. apply closed_vals_weakening. assumption. assumption. *)
(*       simpl+. if_dec. *)
(*       * simpl+ in NI. fsetdec. *)
(*       * crush. *)
(*     + destructs VAL. simp'. split. apply closed_vals_weakening in H. assumption. assumption. *)
(*       simpl+ in H0. if_dec. *)
(*       * simpl+ in NI. fsetdec. *)
(*       * crush. *)
(*   - split; introv VAL; simp' in VAL. *)
(*     + simp'. destructs VAL. splits; crush. *)
(*     + simp'. destructs VAL. splits; crush. *)
(*   - split; introv VAL; simp' in VAL. *)
(*     + simp'. destructs VAL. splits; crush. *)
(*     + simp'. destructs VAL. splits; crush. *)
(*   - split; introv VAL; simp' in VAL. *)
(*     + simp'. simpl+ in NI. destruct VAL as [CV [t1 [t2 [EQ1 [EQ2 VAL]]]]]. split. *)
(*       apply closed_vals_weakening. simpl+. eassumption. assumption. subst. *)
(*       do 2 eexists. splits. 1,2:fequals; dist; subst_notin'; rewrite Sub_app_T_fsk'. *)
(*       rewrite proj1_skvars_codom_rho_Sub. fsetdec. *)
(*       rewrite proj2_skvars_codom_rho_Sub. fsetdec. *)
(*       intros v1 v2 VAL'. specializes VAL v1 v2. *)
(*       (**) *)
(*       forwards [TMTY1 [TMTY2 [v1' [v2' [OP1 [OP2 VAL'']]]]]]: VAL. apply IHτ1 in VAL'. eassumption. fsetdec. *)
(*       splits. 1,2:dist; rewrite Sub_app_T_notinfv_codom; [assumption|rewrite proj1_skvars_codom_rho_Sub||rewrite proj2_skvars_codom_rho_Sub]; fsetdec. *)
(*       (**) *)
(*       exists v1' v2'. splits. 1,2:eauto. apply IHτ2. fsetdec. eassumption. *)
(*     + simp'. simpl+ in NI. destruct VAL as [CV [t1 [t2 [EQ1 [EQ2 VAL]]]]]. split. *)
(*       apply closed_vals_weakening in CV. eassumption. simpl+. assumption. subst. *)
(*       do 2 eexists. splits. 1,2:fequals; dist; subst_notin'; rewrite Sub_app_T_fsk'. *)
(*       rewrite proj1_skvars_codom_rho_Sub. fsetdec. *)
(*       rewrite proj2_skvars_codom_rho_Sub. fsetdec. *)
(*       intros v1 v2 VAL'. specializes VAL v1 v2. *)
(*       (**) *)
(*       forwards [TMTY1 [TMTY2 [v1' [v2' [OP1 [OP2 VAL'']]]]]]: VAL. apply IHτ1. fsetdec. eassumption. splits. *)
(*       dist in TMTY1. rewrite Sub_app_T_notinfv_codom in TMTY1. assumption. rewrite proj1_skvars_codom_rho_Sub. fsetdec. *)
(*       dist in TMTY2. rewrite Sub_app_T_notinfv_codom in TMTY2. assumption. rewrite proj2_skvars_codom_rho_Sub. fsetdec. *)
(*       (**) *)
(*       exists v1' v2'. splits. 1,2:eauto. apply IHτ2 in VAL''. eassumption. fsetdec. *)
(*   - split; introv VAL; simp' in VAL. *)
(*     + simp'. destruct VAL as [CV [t1 [t2 [EQ1 [EQ2 VAL]]]]]. subst. *)
(*       split. apply closed_vals_weakening. assumption. assumption. *)
(*       do 2 eexists. splits. 1,2:reflexivity. intros τ1' τ2' R'. *)
(*       specializes VAL τ1' τ2' R'. destruct VAL as [L VAL]. *)
(*       exists (L ∪ {{α}}). intros β NIL__β RV. *)
(*       (**) *)
(*       specializes VAL β. specializes VAL. fsetdec. eassumption. destruct VAL as [TMTY1 [TMTY2 [v1 [v2 [OP1 [OP2 VAL]]]]]]. *)
(*       dist in TMTY1. dist in TMTY2. simpl+ in H. splits; dist. *)
(*       rewrite Sub_app_Sc_notinfv_codom. assumption. rewrite fsk_Sc_open_Sc_wrt_T_upper. rewrite proj1_skvars_codom_rho_Sub. simpl+. fsetdec. *)
(*       rewrite Sub_app_Sc_notinfv_codom. assumption. rewrite fsk_Sc_open_Sc_wrt_T_upper. rewrite proj2_skvars_codom_rho_Sub. simpl+. fsetdec. *)
(*       exists v1 v2. splits. 1,2:eassumption. *)
(*       apply logrel_val_rho_shuffle. applys IHn. 3:eassumption. simpl+. reflexivity. simpl+. *)
(*       (**) *)
(*       rewrite fsk_Sc_open_Sc_wrt_T_upper. simpl+. destruct RV as [WF1 [WF2 _]]. *)
(*       assert (α ∉ fv__α(τ1')). rewrite WfT_sk. 2:apply WF1. crush. *)
(*       assert (α ∉ fv__α(τ2')). rewrite WfT_sk. 2:apply WF2. crush. *)
(*       fsetdec. *)
(*     + simp'. destruct VAL as [CV [t1 [t2 [EQ1 [EQ2 VAL]]]]]. subst. *)
(*       split. apply closed_vals_weakening in CV. assumption. fsetdec. *)
(*       do 2 eexists. splits. 1,2:reflexivity. intros τ1' τ2' R'. *)
(*       specializes VAL τ1' τ2' R'. destruct VAL as [L VAL]. *)
(*       exists (L ∪ {{α}}). intros β NIL__β RV. *)
(*       (**) *)
(*       specializes VAL β. specializes VAL. fsetdec. eassumption. destruct VAL as [TMTY1 [TMTY2 [v1 [v2 [OP1 [OP2 VAL]]]]]]. *)
(*       dist in TMTY1. dist in TMTY2. splits; dist. *)
(*       rewrite Sub_app_Sc_notinfv_codom in TMTY1. assumption. rewrite fsk_Sc_open_Sc_wrt_T_upper. rewrite proj1_skvars_codom_rho_Sub. simpl+. fsetdec. *)
(*       rewrite Sub_app_Sc_notinfv_codom in TMTY2. assumption. rewrite fsk_Sc_open_Sc_wrt_T_upper. rewrite proj2_skvars_codom_rho_Sub. simpl+. fsetdec. *)
(*       exists v1 v2. splits. 1,2:eassumption. *)
(*       apply logrel_val_rho_shuffle in VAL. apply IHn in VAL. eassumption. simpl+. reflexivity. simpl+. *)
(*       (**) *)
(*       rewrite fsk_Sc_open_Sc_wrt_T_upper. simpl+. destruct RV as [WF1 [WF2 _]]. *)
(*       assert (α ∉ fv__α(τ1')). rewrite WfT_sk. 2:apply WF1. crush. *)
(*       assert (α ∉ fv__α(τ2')). rewrite WfT_sk. 2:apply WF2. crush. *)
(*       fsetdec. *)
(* Qed. *)
