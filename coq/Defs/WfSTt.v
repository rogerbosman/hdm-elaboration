Set Warnings "-notation-overridden,-intuition-auto-with-star".

Require Import Preamble.
Require Import Defs.HdmLems.

Require Import Defs.Freevars.
Require Import Defs.Lc.

(* Require Import Defs.Subst. *)
Require Import Defs.Subst.HdmSubst.
Require Import Defs.Subst.Notation.
Require Import Defs.Subst.rename_name_E.
Require Import Defs.Subst.rename_skvar_E.
Require Import Defs.Subst.subst_skvar_binding_E.

#[export] Hint Unfold WfS WfT : defs.

(*** Unfolding defs *)
Fact Wft_lc : forall ψ t,
    ψ ⊢wft t
  -> lc(t).
Proof. introv WF. unfolds in WF. crush. Qed.
Fact Wft_sk : forall ψ t,
    ψ ⊢wft t
  -> fv__α(t) ⊆ E_A_skvars ψ.
Proof. introv WF. unfolds in WF. crush. Qed.
Fact Wft_names : forall ψ t,
    ψ ⊢wft t
  -> fv__x( t ) ⊆ E_names ψ.
Proof. introv WF. unfolds in WF. crush. Qed.
Fact WfT_lc : forall ψ τ,
    ψ ⊢wfτ τ
  -> lc(τ).
Proof. introv WF. unfolds in WF. crush. Qed.
Fact WfT_sk : forall ψ τ,
    ψ ⊢wfτ τ
  -> fv__α(τ) ⊆ E_A_skvars ψ.
Proof. introv WF. unfolds in WF. crush. Qed.
Fact WfS_lc : forall ψ σ,
    ψ ⊢wfσ σ
  -> lc(σ).
Proof. introv WF. unfolds in WF. crush. Qed.
Fact WfS_sk : forall ψ σ,
    ψ ⊢wfσ σ
  -> fv__α(σ) ⊆ E_A_skvars ψ.
Proof. introv WF. unfolds in WF. crush. Qed.
#[export] Hint Resolve Wft_lc Wft_sk Wft_names WfT_lc WfT_sk WfS_lc WfS_sk : core.

Fact Wft_sk_eq : forall t,
    • ⊢wft t
  -> fv__α(t) ≡ (∅).
Proof. introv WF. apply Wft_sk in WF. simpl+ in WF. fsetdec. Qed.
Fact Wft_names_eq : forall t,
    • ⊢wft t
  -> fv__x( t ) ≡ (∅).
Proof. introv WF. apply Wft_names in WF. simpl+ in WF. fsetdec. Qed.
Fact WfT_sk_eq : forall τ,
    • ⊢wfτ τ
  -> fv__α(τ) ≡ (∅).
Proof. introv WF. apply WfT_sk in WF. simpl+ in WF. fsetdec. Qed.
Fact WfS_sk_eq : forall σ,
    • ⊢wfσ σ
  -> fv__α(σ) ≡ (∅).
Proof. introv WF. apply WfS_sk in WF. simpl+ in WF. fsetdec. Qed.
#[export] Hint Rewrite Wft_sk_eq Wft_names_eq WfT_sk_eq WfS_sk_eq : fv_empty.

Ltac fv_empty' := autorewrite with fv_empty.
(* Ltac fv_empty' := *)
(*   match goal with *)
(*     | [ |- context[fv__α( ?x ) ] ]  => *)
(*         match type of x with *)
(*         | Sc => rewrite (WfS_sk_eq) *)
(*         | T  => rewrite (WfT_sk_eq) *)
(*         | Tm => rewrite (Wft_sk_eq) *)
(*         end *)
(*     | [ |- context[fv__x( ?x ) ] ]  => *)
(*         match type of x with *)
(*         | Tm => rewrite (Wft_names •) *)
(*         end *)
(*     end. *)
Ltac fv_empty := fv_empty'; eauto.

(** Dumb hints because (e)auto isn't smart enough *)
Fact closed_Tm_notinfvx : forall x t,
    • ⊢wft t
  -> x ∉ fv__x(t).
Proof. intros. fv_empty. Qed.
#[export] Hint Resolve closed_Tm_notinfvx : core.

Lemma closed_Tm_disj : forall t L,
    • ⊢wft t
  -> fv__α(t) ∐ L.
Proof. intros. fv_empty. Qed.
#[export] Hint Resolve closed_Tm_disj : core.

(** Replaced by WfT_sk *)
(* Axiom WfT_sk_sub : forall ψ τ, *)
(*     ψ ⊢wfτ τ *)
(*   -> fv__α(τ) ⊆ E_A_skvars ψ. *)
(*** Constructing *)
Axiom WfT_Fun : forall ψ τ1 τ2,
    ψ ⊢wfτ T__Fun τ1 τ2
  <-> ψ ⊢wfτ τ1
  /\ ψ ⊢wfτ τ2.
#[export] Hint Rewrite WfT_Fun : core.
Corollary WfT_Fun1 : forall ψ τ1 τ2,
    ψ ⊢wfτ T__Fun τ1 τ2
  -> ψ ⊢wfτ τ1.
Proof. intros. simpl+ in H. jauto. Qed.
Corollary WfT_Fun2 : forall ψ τ1 τ2,
    ψ ⊢wfτ T__Fun τ1 τ2
  -> ψ ⊢wfτ τ2.
Proof. intros. simpl+ in H. jauto. Qed.
#[export] Hint Resolve WfT_Fun1 WfT_Fun2 : core.

Fact Wft_app : forall ψ t1 t2,
    ψ ⊢wft t__App t1 t2
  <-> ψ ⊢wft t1
  /\ ψ ⊢wft t2.
Proof.
  unfold Wft. intros.
  split; intros.
  - destructs H. simpl+ in *. splits. splits. eauto. fsetdec. fsetdec. eauto. fsetdec. fsetdec.
  - splits. crush. simpl+. fsetdec. simpl+. fsetdec.
Qed.
#[export] Hint Rewrite Wft_app : core.
Corollary Wft_app1 : forall ψ t1 t2,
    ψ ⊢wft t__App t1 t2
  -> ψ ⊢wft t1.
Proof. intros. simpl+ in H. jauto. Qed.
Corollary Wft_app2 : forall ψ t1 t2,
    ψ ⊢wft t__App t1 t2
  -> ψ ⊢wft t2.
Proof. intros. simpl+ in H. jauto. Qed.
#[export] Hint Resolve Wft_app1 Wft_app2 : core.

Fact Wft_var : forall ψ x,
    x ∈ E_names ψ
  -> ψ ⊢wft t__Var_f x.
Proof. intros. splits. crush. simpl+. fsetdec. simpl+. fsetdec. Qed.

Fact Wft_tapp : forall ψ t τ,
    ψ ⊢wft t__TApp t τ
  <-> ψ ⊢wft t
  /\ ψ ⊢wfτ τ.
Proof.
  unfold WfT. unfold Wft. split; intros; splits. simpl+ in H.
  - destr. splits. inverts LC. crush. fsetdec. fsetdec.
  - destr. inverts LC. crush.
  - simpl+ in H. destr. fsetdec.
  - simpl+ in H. constructor. jauto. jauto.
  - simpl+ in H. simpl+. fsetdec.
  - simpl+ in H. simpl+. fsetdec.
Qed.

Fact Wft_lam : forall ψ τ1 t2 x σ,
    (ψ ::x x :- σ) ⊢wft (open_Tm_wrt_Tm t2 (t__Var_f x))
  -> x ∉ fv__x(t2)
  -> ψ ⊢wfτ τ1
  -> ψ ⊢wft t__Lam τ1 t2.
Proof.
  unfold WfT. unfold Wft. intros; splits; destr.
  - eapply lc_t__Lam_exists. jauto. jauto.
  - simpl+. simpl+ in SUB0. rewrite <- fsk_Tm_open_Tm_wrt_Tm_lower in SUB0. fsetdec.
  - simpl+. simpl+ in SUB1. rewrite <- ftv_Tm_open_Tm_wrt_Tm_lower in SUB1. fsetdec.
Qed.

Fact Wft_strengthen : forall ψ x σ t,
    (ψ ::x x :- σ) ⊢wft t
  -> x ∉ fv__x(t)
  -> ψ ⊢wft t.
Proof. intros. unfold Wft in *. simpl+ in *. destr. splits. crush. crush. fsetdec. Qed.

Fact Wft_open_Tm_wrt_Tm : forall ψ t1 t2 x σ,
    (ψ ::x x :- σ) ⊢wft open_Tm_wrt_Tm t1 (t__Var_f x)
  -> ψ  ⊢wft t2
  -> x ∉ fv__x(t1)
  -> ψ ⊢wft open_Tm_wrt_Tm t1 t2.
Proof.
  unfold Wft. intros; splits; destr.
  - eapply lc_body_Tm_wrt_Tm. 2:jauto. unfolds. intros.
    forwards: subst_tvar_Tm_lc_Tm (open_Tm_wrt_Tm t1 (t__Var_f x)) (t__Var_f tx1) x. eassumption.
    crush. rewrite subst_tvar_Tm_open_Tm_wrt_Tm in H. simpl+ in H. if_taut.
    applys_eq H. fequals. symmetry. apply subst_tvar_Tm_notin. crush. crush.
  - simpl+. simpl+ in SUB1. rewrite fsk_Tm_open_Tm_wrt_Tm_upper.
    rewrite <- fsk_Tm_open_Tm_wrt_Tm_lower in SUB1.
    fsetdec.
  - simpl+ in *. rewrite ftv_Tm_open_Tm_wrt_Tm_upper.
    rewrite <- ftv_Tm_open_Tm_wrt_Tm_lower in *. fsetdec.
Qed.

Fact WfST : forall ψ τ,
    ψ ⊢wfτ τ <-> ψ ⊢wfσ S__T τ.
Proof. unfold WfS. unfold WfT. crush. Qed.
Corollary WfST1 : forall ψ τ, ψ ⊢wfτ τ -> ψ ⊢wfσ S__T τ. apply WfST. Qed.
Corollary WfST2 : forall ψ τ, ψ ⊢wfσ S__T τ -> ψ ⊢wfτ τ. apply WfST. Qed.
#[export] Hint Resolve WfST1 WfST2 : core.

Fact Wft_unit : forall ψ,
    ψ ⊢wft t__Unit.
Proof. split; crush. Qed.
#[export] Hint Resolve Wft_unit : core.

Fact WfT_var : forall ψ α,
    α ∈ E_A_skvars ψ
  -> ψ ⊢wfτ T__Var_f α.
Proof. intros. split. crush. simpl+. fsetdec. Qed.

Fact WfS_var : forall ψ α,
    α ∈ E_A_skvars ψ
  -> ψ ⊢wfσ S__T (T__Var_f α).
Proof. intros. apply WfST1. auto using WfT_var. Qed.

Lemma WfS_open_Sc_wrt_T' : forall ψ σ α,
    ψ ⊢wfσ S__Forall σ
  -> (ψ ::a [α]) ⊢wfσ open_Sc_wrt_T σ (T__Var_f α).
Proof.
  intros. split. crush. rewrite fsk_Sc_open_Sc_wrt_T_upper.
  apply WfS_sk in H. simpl+. fsetdec.
Qed.


(*** Open/close *)
Lemma close_Sc_wrt_A_WfTy : forall ψ σ a,
    (ψ ::a a) ⊢wfσ σ
  -> ψ ⊢wfσ (close_Sc_wrt_A σ a).
Proof.
  introv [LC FV]. split. eauto using close_Sc_wrt_A_lc.
  rewrite fsk_close_Sc_wrt_A. simpl+ in FV. fsetdec.
Qed.

(*** Subst *)
Lemma WfT_subst_name : forall x__in x__out ψ τ,
    ψ ⊢wfτ τ
  -> ({x__in ↤__x x__out}ψ) ⊢wfτ τ.
Proof. introv WF. splits; simpl+; jauto. Qed.

Lemma WfT_rename_skvar_E : forall τ β α ψ,
     ψ ⊢wfτ τ
  -> ({β ↤ α}ψ) ⊢wfτ ({T__Var_f β ≔ α} τ).
Proof.
  intros. split. crush. decide_in α (fv__α(τ)).
  - destruct H as [_ SUB].
    rewrite E_A_skvars_rename_skvar_E_in. 2:fsetdec.
    rewrite fsk_T_subst_skvar_T_upper. simpl+. fsetdec.
  - rewrite subst_skvar_T_notin. 2:eassumption.
    rewrite <- E_A_skvars_rename_skvar_E_lower. fsetdec+.
Qed.

(*** Random *)
Lemma closed_Sc : forall σ,
    • ⊢wfσ σ
  -> fv__α(σ) ≡ ∅.
Proof. introv WFS. apply WfS_sk in WFS. fsetdec. Qed.
#[export] Hint Resolve closed_Sc : core.

Lemma WfT_subst_skvar_binding_E : forall (α : skvar) (τ1 τ2 : T) (ψ : E),
    remove_sk_E α ψ ⊢wfτ τ1
  -> ψ ⊢wfτ τ2
  -> {τ1 ⇏ α} ψ ⊢wfτ ({τ1 ≔ α} τ2).
Proof.
  introv WFT. constructor. crush.
  rewrite fsk_T_subst_skvar_T_upper.
  apply WfT_sk in WFT. apply WfT_sk in H. simpl+ in WFT.
  rewrite E_A_skvars_subst_skvar_binding_E_lower. fsetdec.
Qed.
