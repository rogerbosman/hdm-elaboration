Set Warnings "-notation-overridden,-intuition-auto-with-star".

Require Import Preamble.
(* Require Import Defs.HdmLems. *)

Require Import Defs.E.
Require Import Defs.ELookup.
Require Import Defs.ERels.
(* Require Import Defs.Foralls. *)
Require Import Defs.List.
Require Import Defs.Lc.
Require Import Defs.TmTy.
Require Import Defs.WfSTt.
Require Import Defs.Sub.
Require Import Defs.Subx.

Require Import Semantics.ClosedVals.
Require Import Semantics.gammaDef.
Require Import Semantics.LogRel.
(* Require Import Semantics.Opsem. *)
Require Import Semantics.rho.

(* From Equations Require Import Equations. *)

Lemma logrel_E_dom_gamma : forall ρ γ ψ,
    ⦅ρ, γ⦆ ∈ ⦅𝒟, 𝒢⦆⟦ψ⟧
  -> dom_gamma γ ≡ E_names ψ.
Proof.
  introv IN. gen ρ γ. induction ψ. 2:induction a. all:intros; simp' in IN.
  - inverts IN. simpl+. crush.
  - simpl+. eauto.
  - simpl+. destr_logrel_val IN. simpl+ in IHa. rewrite IHa. fsetdec. eauto.
  - simpl+. destr_logrel_val IN. simpl+. rewrite IHψ. fsetdec. eauto.
  - simpl+. eauto.
Qed.

(*** Lc *)
Lemma logrel_E_lc : forall ρ γ ψ,
    ⦅ρ, γ⦆ ∈ ⦅𝒟, 𝒢⦆⟦ψ⟧
  -> lc(ρ) /\ lc(γ).
Proof.
  introv IN. gen ρ γ. induction ψ. 2:induction a. all:intros; simp' in IN.
  - destruct IN. crush.
  - destr_logrel_val IN. forwards: IHa. eassumption.
    split. 2:jauto. apply rho_lc_cons; jauto.
  - destr_logrel_val IN. forwards: IHψ. eassumption.
    split. jauto. apply gamma_lc_cons; jauto.
Qed.

Lemma logrel_E_lc_rho : forall ρ γ ψ,
    ⦅ρ, γ⦆ ∈ ⦅𝒟, 𝒢⦆⟦ψ⟧
  -> lc(ρ).
Proof. intros. apply logrel_E_lc in H. jauto. Qed.
Lemma logrel_E_lc_gamma : forall ρ γ ψ,
    ⦅ρ, γ⦆ ∈ ⦅𝒟, 𝒢⦆⟦ψ⟧
  -> lc(γ).
Proof. intros. apply logrel_E_lc in H. jauto. Qed.
#[export] Hint Resolve logrel_E_lc_rho logrel_E_lc_gamma : core.


(*** WfT Closing *)
Lemma T_close1 : forall τ ψ ρ,
    ψ ⊢wfτ τ
  -> ρ ∈ 𝒟⟦ψ⟧
  -> • ⊢wfτ ⟦π1 ρ ▹ τ⟧.
Proof.
  introv WF [γ IN]. split.
  - eauto using Sub_app_T_lc.
  - rewrite Sub_app_T_fsk. simpl+.
    erewrite WfT_sk. 2:eassumption.
    rewrite proj1_skvars_codom_rho_Sub. rewrite logrel_E_skvars_codom_rho_empty. 2:eauto.
    rewrite proj1_dom_rho_Sub. rewrite logrel_E_dom_rho_E_A_skvars. 2:eauto.
    fsetdec.
Qed.

Lemma T_close2 : forall τ ψ ρ,
    ψ ⊢wfτ τ
  -> ρ ∈ 𝒟⟦ψ⟧
  -> • ⊢wfτ ⟦π2 ρ ▹ τ⟧.
Proof.
  introv WF [γ IN]. split.
  - eauto using Sub_app_T_lc.
  - rewrite Sub_app_T_fsk. simpl+.
    erewrite WfT_sk. 2:eassumption.
    rewrite proj2_skvars_codom_rho_Sub. rewrite logrel_E_skvars_codom_rho_empty. 2:eauto.
    rewrite proj2_dom_rho_Sub. rewrite logrel_E_dom_rho_E_A_skvars. 2:eauto.
    fsetdec.
Qed.

(*** TmTy Closing *)

Axiom TmTy_close_app1_names_admit:
  forall (ψ1 : E) (x : atom) (σ : Sc) (ψ2 : E) (ρ : rho) (γ : gamma), ⦅ρ, γ⦆ ∈ ⦅𝒟, 𝒢⦆⟦ψ1 ::x x :- σ⟧ -> x ∉ E_names ⟦π1 ρ ▹ ψ2⟧.

Lemma TmTy_close_app1 : forall ψ1 ψ2 t σ ρ γ,
    ψ1 +++ ψ2 ⊢t t ▸ σ
  -> ⦅ρ, γ⦆ ∈ ⦅𝒟, 𝒢⦆⟦ψ1⟧
  -> ⟦π1 ρ ▹ ψ2⟧ ⊢t ⟦π1 ρ ▹ ⟦π1 γ ▹__x  t⟧⟧ ▸ ⟦π1 ρ ▹ σ⟧.
Proof.
  intro ψ1. induction ψ1. 2:ind_a a. all:introv TMTY IN.
  - destruct ρ. 2:simp' in IN; crush.
    destruct γ. 2:simp' in IN; crush.
    simpl+. crush.
  - apply IHψ1.
    + eapply TmTy_weaken. eassumption. unfolds. simpl+. reflexivity.
      unfolds. intros. forwards [? |[? ?]]: E_lookup_distr. eassumption. crush. simpl+ in H1. eauto with elookup.
    + simp' in IN.
  - simp' in IN. destruct IN as [τ1 [τ2 [R [ρ' [EQ [VAL [NID IN]]]]]]].
    rewrite <- proj1_dom_rho_Sub in NID.
    forwards: IHa ((• ::a [α]) +++ ψ2). eapply TmTy_weaken. apply TMTY. unfolds. simpl+. fsetdec.
    unfolds. intros. forwards [? |[? ?]]: E_lookup_distr. eassumption. crush. simpl+ in H1. eapply E_lookup_app__r. simpl+. eassumption. simpl+.
    rewrite E_lookup_none__r. crush. eassumption. eassumption.
    apply (TmTy_subst_skvar_binding_E τ1 α) in H.
    + subst. simpl+. dist in H.
      rewrite Sub_app_E_notindom in H. 2:simpl+; fsetdec. simpl+ in H. if_taut.
      eapply TmTy_weaken.
      * applys_eq H. dist. reflexivity.
      * unfolds. simpl+. crush.
      * unfolds. introv LU. simpl+ in LU. forwards [? |[? ?]]: E_lookup_distr LU.
        crush. simpl+ in H1. inverts H1.
    + eapply (WfT_E_A_sk_sub •). unfolds in VAL. jauto. unfolds. fsetdec.
  - assert (NIE: x ∉ E_names ⟦π1 ρ ▹ ψ2⟧). eauto using TmTy_close_app1_names_admit.
    simp' in IN. destruct IN as [v1 [v2 [γ' [EQ [VAL [NID IN]]]]]].
    forwards: IHψ1 ((• ::x x :- σ) +++ ψ2). applys_eq TMTY. simpl+. reflexivity. eassumption.
    dist in H. eapply (TmTy_subst_name v1 x ⟦π1 ρ ▹ σ⟧) in H.
    + applys_eq H.
      * simpl+. if_taut. simpl+. rewrite remove_var_E_notin. reflexivity. assumption.
      * rewrite EQ. simpl+. rewrite Sub_app_Tm_subst_tvar_Tm. reflexivity. fv_empty.
    + simpl+. apply E_lookup_app__r. simpl+. if_taut. eauto.
    + apply (TmTy_weaken •). eauto. unfolds. fsetdec.
      unfolds. intros. simpl+ in H0. inverts H0.
  - eapply IHψ1. eapply TmTy_weaken. eassumption. unfolds. simpl+. reflexivity.
    unfolds. intros. forwards [? |[? ?]]: E_lookup_distr. eassumption. crush. simpl+ in H1. eauto with elookup.
    simp' in IN.
Qed.

Corollary TmTy_close1 : forall ψ t σ ρ γ,
    ψ ⊢t t ▸ σ
  -> ⦅ρ, γ⦆ ∈ ⦅𝒟, 𝒢⦆⟦ψ⟧
  -> • ⊢t ⟦π1 ρ ▹ ⟦π1 γ ▹__x  t⟧⟧ ▸ ⟦π1 ρ ▹ σ⟧.
Proof.
  introv DEC IN. forwards: TmTy_close_app1 ψ •. applys_eq DEC. eassumption.
  applys_eq H. simpl+. reflexivity.
Qed.

Axiom TmTy_close_app2_names_admit:
  forall (ψ1 : E) (x : atom) (σ : Sc) (ψ2 : E) (ρ : rho) (γ : gamma), ⦅ρ, γ⦆ ∈ ⦅𝒟, 𝒢⦆⟦ψ1 ::x x :- σ⟧ -> x ∉ E_names ⟦π2 ρ ▹ ψ2⟧.

Lemma TmTy_close_app2 : forall ψ1 ψ2 t σ ρ γ,
    ψ1 +++ ψ2 ⊢t t ▸ σ
  -> ⦅ρ, γ⦆ ∈ ⦅𝒟, 𝒢⦆⟦ψ1⟧
  -> ⟦π2 ρ ▹ ψ2⟧ ⊢t ⟦π2 ρ ▹ ⟦π2 γ ▹__x  t⟧⟧ ▸ ⟦π2 ρ ▹ σ⟧.
Proof.
  intro ψ1. induction ψ1. 2:ind_a a. all:introv TMTY IN.
  - destruct ρ. 2:simp' in IN; crush.
    destruct γ. 2:simp' in IN; crush.
    simpl+. crush.
  - apply IHψ1.
    + eapply TmTy_weaken. eassumption. unfolds. simpl+. reflexivity.
      unfolds. intros. forwards [? |[? ?]]: E_lookup_distr. eassumption. crush. simpl+ in H1. eauto with elookup.
    + simp' in IN.
  - simp' in IN. destruct IN as [τ1 [τ2 [R [ρ' [EQ [VAL [NID IN]]]]]]].
    rewrite <- proj2_dom_rho_Sub in NID.
    forwards: IHa ((• ::a [α]) +++ ψ2). eapply TmTy_weaken. apply TMTY. unfolds. simpl+. fsetdec.
    unfolds. intros. forwards [? |[? ?]]: E_lookup_distr. eassumption. crush. simpl+ in H1. eapply E_lookup_app__r. simpl+. eassumption. simpl+.
    rewrite E_lookup_none__r. crush. eassumption. eassumption.
    apply (TmTy_subst_skvar_binding_E τ2 α) in H.
    + subst. simpl+. dist in H.
      rewrite Sub_app_E_notindom in H. 2:simpl+; fsetdec. simpl+ in H. if_taut.
      eapply TmTy_weaken.
      * applys_eq H. dist. reflexivity.
      * unfolds. simpl+. crush.
      * unfolds. introv LU. simpl+ in LU. forwards [? |[? ?]]: E_lookup_distr LU.
        crush. simpl+ in H1. inverts H1.
    + eapply (WfT_E_A_sk_sub •). unfolds in VAL. jauto. unfolds. fsetdec.
  - assert (NIE: x ∉ E_names ⟦π2 ρ ▹ ψ2⟧). eauto using TmTy_close_app2_names_admit.
    simp' in IN. destruct IN as [v1 [v2 [γ' [EQ [VAL [NID IN]]]]]].
    forwards: IHψ1 ((• ::x x :- σ) +++ ψ2). applys_eq TMTY. simpl+. reflexivity. eassumption.
    dist in H. eapply (TmTy_subst_name v2 x ⟦π2 ρ ▹ σ⟧) in H.
    + applys_eq H.
      * simpl+. if_taut. simpl+. rewrite remove_var_E_notin. reflexivity. assumption.
      * rewrite EQ. simpl+. rewrite Sub_app_Tm_subst_tvar_Tm. reflexivity. fv_empty.
    + simpl+. apply E_lookup_app__r. simpl+. if_taut. eauto.
    + apply (TmTy_weaken •). eauto. unfolds. fsetdec.
      unfolds. intros. simpl+ in H0. inverts H0.
  - eapply IHψ1. eapply TmTy_weaken. eassumption. unfolds. simpl+. reflexivity.
    unfolds. intros. forwards [? |[? ?]]: E_lookup_distr. eassumption. crush. simpl+ in H1. eauto with elookup.
    simp' in IN.
Qed.

Corollary TmTy_close2 : forall ψ t σ ρ γ,
    ψ ⊢t t ▸ σ
  -> ⦅ρ, γ⦆ ∈ ⦅𝒟, 𝒢⦆⟦ψ⟧
  -> • ⊢t ⟦π2 ρ ▹ ⟦π2 γ ▹__x  t⟧⟧ ▸ ⟦π2 ρ ▹ σ⟧.
Proof.
  introv DEC IN. forwards: TmTy_close_app2 ψ •. applys_eq DEC. eassumption.
  applys_eq H. simpl+. reflexivity.
Qed.
