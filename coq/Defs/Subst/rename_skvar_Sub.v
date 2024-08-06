Set Warnings "-notation-overridden,-intuition-auto-with-star".
Require Import Preamble.
Require Import Defs.HdmLems.

Require Import Defs.Subst.Notation.
Require Import Defs.Subst.rename_var.

Require Import Defs.Subst.HdmSubst.
Require Import Defs.Subst.rename_skvar_A.

Require Import Defs.Sub.

Definition rename_skvar_Sub (α__in α__out : skvar) : Sub -> Sub :=
  map (fun p => ({T__Var_f α__in ≔ α__out} (fst p), rename_var α__in α__out (snd p))).
#[export] Instance renamable_skvar_Sub : renamable_skvar Sub skvar := { rename_skvar := rename_skvar_Sub }.

Lemma rename_skvar_Sub_rename_skvar_Sub_samevar : forall θ α1 α2 α3,
    α1 ∉ dom_Sub θ
  -> α2 ∉ dom_Sub θ ∪ skvars_codom_Sub θ
  -> {α3 ↤ α2}({α2 ↤ α1}θ) = {α3 ↤ α1}θ.
Proof.
  intro θ. ind_Sub θ; introv NID1 NID2. crush.
  simpl+ in  *. rewrite IHθ. 2:fsetdec. 2:fsetdec. unfold rename_var.
  destruct (α == α1). subst. fsetdec.
  destruct (α == α2). subst. fsetdec.
  rewrite subst_skvar_T_subst_skvar_T_samevar. reflexivity. fsetdec.
Qed.

Lemma rename_skvar_Sub_Sub_app_T : forall α β θ (τ:T),
    β ∉ fv__α(τ) ∪ skvars_codom_Sub θ ∪ dom_Sub θ
  -> {T__Var_f β ≔ α}(⟦θ ▹ τ⟧) = ⟦{β ↤ α}θ ▹ {T__Var_f β ≔ α}τ⟧.
Proof.
  intros α β θ. gen α β. ind_Sub θ. crush.
  introv NI. simpl+ in *.
  dist. rewrite <- IHθ. 2:fsetdec. destruct (α0 == α).
  - subst. unfold rename_var. if_taut.
    rewrite subst_skvar_T_subst_skvar_T_samevar. 2:eauto.
    apply subst_skvar_T_subst_skvar_T_samevar'.
    rewrite Sub_app_T_fsk'. fsetdec.
  - rewrite <- subst_skvar_T_subst_skvar_T; unfold rename_var in *. if_taut. reflexivity.
    if_taut. simpl+. clear - NI. fsetdec.
    if_taut.
Qed.

Lemma rename_skvar_Sub_Sub_app_T' : forall α β θ (τ:T),
    β ∉ fv__α(τ) ∪ skvars_codom_Sub θ ∪ dom_Sub θ
  -> α ∉ fv__α(τ)
  -> {T__Var_f β ≔ α}(⟦θ ▹ τ⟧) = ⟦{β ↤ α}θ ▹ τ⟧.
Proof. introv NIL1 NIL2. rewrite rename_skvar_Sub_Sub_app_T. subst_notin. assumption. Qed.

Lemma rename_skvar_Sub_Sub_to_A : forall α β θ,
    {β ↤ α}Sub_to_A θ = Sub_to_A ({β ↤ α}θ).
Proof. intros. ind_Sub θ. crush. simpl+. rewrite IHθ. crush. Qed.

Lemma rename_skvar_Sub_Sub_to_A_notin : forall α β θ,
    α ∉ dom_Sub θ
  -> Sub_to_A ({β ↤ α}θ) = Sub_to_A θ.
Proof. intros. rewrite <- rename_skvar_Sub_Sub_to_A. apply rename_skvar_A_notin. rewrite varl_Sub_to_A_dom. assumption. Qed.

Lemma rename_skvar_Sub_Sub_app_Tm : forall α β θ (t:Tm),
    β ∉ fv__α(t) ∪ skvars_codom_Sub θ ∪ dom_Sub θ
  -> {T__Var_f β ≔ α}(⟦θ ▹ t⟧) = ⟦{β ↤ α}θ ▹ {T__Var_f β ≔ α}t⟧.
Proof.
  introv NI. gen α β. ind_Sub θ; intros. simpl+. crush.
  dist. simpl+ in NI. rewrite <- IHθ. 2:fsetdec. unfold rename_var. if_dec.
  - rewrite subst_skvar_Tm_subst_skvar_Tm_samevar.
    2:rewrite Sub_app_Tm_fsk'; fsetdec.
    apply subst_skvar_Tm_subst_skvar_Tm_samevar'.
  - rewrite <- subst_skvar_Tm_subst_skvar_Tm; unfold rename_var in *. if_taut. reflexivity.
    if_taut. simpl+. clear - NI. fsetdec. crush.
Qed.

Lemma rename_skvar_Sub_Sub_app_Tm' : forall α β θ (t:Tm),
    β ∉ fv__α(t) ∪ skvars_codom_Sub θ ∪ dom_Sub θ
  -> α ∉ fv__α(t)
  -> {T__Var_f β ≔ α}(⟦θ ▹ t⟧) = ⟦{β ↤ α}θ ▹ t⟧.
Proof. introv NIL1 NIL2. rewrite rename_skvar_Sub_Sub_app_Tm. 2:assumption. subst_notin. Qed.
