Set Warnings "-notation-overridden,-intuition-auto-with-star".

Require Import Preamble.
Require Import Preamble.Tag.

Require Import Defs.EInst.
Require Import Defs.FrA.
Require Import Defs.List.
Require Import Defs.Sub.
Require Import Defs.WfE.

Fact uni_Sub_app : forall θ1 θ2,
    uni_Sub θ1
  -> uni_Sub θ2
  -> dom_Sub θ1 ∐ dom_Sub θ2
  -> uni_Sub (θ1 ++ θ2).
Proof.
  introv UN1 UN2 DISJ. unfold uni_Sub in *. intros.
  simpl+ in H. destr_union; simpl+ in H0; destr_union. all:try inverts H; try inverts H0.
  - eauto.
  - false. applys in_disj DISJ; eauto.
  - false. applys in_disj DISJ; eauto.
  - eauto.
Qed.

Fact union_inter_distr1 : forall L1 L2 L3,
    L1 ∩ (L2 ∪ L3) ≡ (L1 ∩ L2) ∪ (L1 ∩ L3).
Proof. intros. fsetdec. Qed.

Fact union_inter_distr2 : forall L1 L2 L3,
    L1 ∪ (L2 ∩ L3) ≡ (L1 ∪ L2) ∩ (L1 ∪ L3).
Proof. intros. fsetdec. Qed.

(* Fact disj_union_union : forall L1 L1' L2 L2', *)
(*     L1 ∐ L2 *)
(*   -> L1' ∐ L2' *)
(*   -> L1 ∪ L1' ∐ L2 ∪ L2'. *)
(* Proof. *)
(*   intros. unfold disjoint in *. *)
(*   rewrite union_inter_distr1. *)

Definition P_Sub' (θ:Sub) := uni_Sub θ /\ alg_to_dec θ.
Fact P_Sub'_uni : forall θ, P_Sub' θ -> uni_Sub θ. crush. Qed.
Fact P_Sub'_atd : forall θ, P_Sub' θ -> alg_to_dec θ. crush. Qed.
#[export] Hint Resolve P_Sub'_uni P_Sub'_atd : core.

#[export] Hint Resolve alg_to_dec_dom_codom_disj_Sub : core.

Lemma P_Sub'_P_Sub : forall θ, P_Sub' θ -> P_Sub θ.
Proof. intros. split; eauto. Qed.
#[export] Hint Resolve P_Sub'_P_Sub : core.

Fact alg_to_dec_app : forall θ1 θ2,
    alg_to_dec θ1
  -> alg_to_dec θ2
  -> alg_to_dec (θ1 ++ θ2).
Proof. unfold alg_to_dec. intros. simpl+. crush. Qed.

Lemma P_Sub'_app : forall θ1 θ2,
    P_Sub' θ1
  -> P_Sub' θ2
  -> dom_Sub θ1 ∐ dom_Sub θ2
  -> P_Sub' (θ1 ++ θ2).
Proof. intros. split; eauto using uni_Sub_app, alg_to_dec_app. Qed.

Lemma NodDup_Sub_to_A_uni_Sub : forall θ,
    NoDup (Sub_to_A θ)
  -> uni_Sub θ.
Proof. intros. eauto. Qed.
#[export] Hint Resolve NodDup_Sub_to_A_uni_Sub : core.

Definition E_A_skvars_list : E -> A := E_fold [] (flip (app (A := var))) const2 const3.

#[export] Hint Constructors NoDup : core.

Lemma EInst_E_A_skvars_list : forall ψ ψ__dec θ,
    {•, []} ⊢e ψ ⤳ {ψ__dec, θ}
  -> Sub_to_A θ = E_A_skvars_list ψ.
Proof.
  introv EINST. induction EINST.
  - crush.
  - simpl+. forwards: AInst_Sub_to_A. eassumption. subst.
    rewrite IHEINST. simpl+. crush.
  - simpl+. crush.
  - simpl+. crush.
Qed.


Fact varl_E_A_skvars_list : forall ψ,
    varl (E_A_skvars_list ψ) ⊆ E_skvars ψ.
Proof.
  intros. induction ψ; simpl+ in *. 1,3,4: crush.
  rewrite IHψ. reflexivity.
Qed.

Lemma FrA_NoDup_E_A_skvars_list : forall a ψ,
    NoDup (E_A_skvars_list ψ)
  -> a ### E_skvars ψ
  -> NoDup (a ++ E_A_skvars_list ψ).
Proof.
  intro a. ind_a a. crush. intros. simpl+.
  constructor. 2:eauto. apply notin_varl_notin_a. simpl+.
  unfold not. intros. destr_union. inverts H0. inverts H2. apply H5. eauto.
  applys in_disj α. apply FrA_props2. eassumption. simpl+. fsetdec.
  rewrite <- varl_E_A_skvars_list. eassumption.
Qed.

Lemma E_A_skvars_wf_NoDup : forall ψ,
    wf(ψ)
  -> NoDup (E_A_skvars_list ψ).
Proof.
  intro ψ. induction ψ; introv WF; inverts WF.
  - crush.
  - simpl+. eauto using FrA_NoDup_E_A_skvars_list.
  - crush.
  - crush.
Qed.

Lemma EInst_uni_Sub : forall ψ ψ__dec θ,
    {•, []} ⊢e ψ ⤳ {ψ__dec, θ}
  -> wf(ψ)
  -> uni_Sub θ.
Proof.
  intros. apply uni_Sub_nd_uni_Sub. unfolds.
  applys_eq E_A_skvars_wf_NoDup. 2:eassumption. eauto using EInst_E_A_skvars_list.
Qed.

Lemma EInst_dom_Sub : forall ψ__in θ__in ψ ψ__dec θ,
    {ψ__in, θ__in} ⊢e ψ ⤳ {ψ__dec, θ}
  -> dom_Sub θ ≡ E_A_skvars ψ.
Proof.
  introv EINST. induction EINST.
  - crush.
  - simpl+. forwards: AInst_Sub_to_A. eassumption. subst.
    rewrite IHEINST. simpl+. crush.
  - simpl+. crush.
  - simpl+. crush.
Qed.

Lemma EInst_P_Sub' : forall ψ ψ__dec θ,
    {•, []} ⊢e ψ ⤳ {ψ__dec, θ}
  -> wf(ψ)
  -> alg_E ψ
  -> dec_E ψ__dec
  -> P_Sub' θ.
Proof.
  intros. splits. eauto using EInst_uni_Sub.
  eapply EInst_alg_to_dec'; eassumption.
Qed.

Lemma uni_Sub_bindings_Sub : forall θ1 θ2,
    uni_Sub θ2
  -> bindings_Sub_sub θ1 θ2
  -> uni_Sub θ1.
Proof. unfold uni_Sub. intros. unfolds in H0. applys H α; fsetdec'. Qed.


Lemma bindings_Sub_sub_dom_Sub_sub : forall θ1 θ2,
    bindings_Sub θ1 ⊆τx bindings_Sub θ2
  -> dom_Sub θ1 ⊆ dom_Sub θ2.
Proof.
  introv SUB. unfolds in SUB. unfolds. intros.
  - forwards [τ IN]: dom_Sub_bindings_Sub. eassumption.
    eapply bindings_Sub_dom_Sub2. apply SUB. eauto.
Qed.

#[export] Instance bindings_Sub_sub_dom_Sub_sub_proper : Proper (bindings_Sub_sub ==> Subset) dom_Sub.
Proof. autounfold. intros. eauto using bindings_Sub_sub_dom_Sub_sub. Qed.



Lemma skvars_codom_Sub_bindings_Sub : forall (α:skvar) (θ:Sub),
    α ∈ skvars_codom_Sub θ
  -> exists β τ, (τ, β) ∈τx bindings_Sub θ /\ α ∈ fv__α(τ).
Proof.
  intros. ind_Sub θ. crush.
  simpl+ in H. destr_union.
  - exists α0 τ. split. simpl+. fsetdec. assumption.
  - specializes IHθ. simpl+ in H. fsetdec.
    destr. exists β τ0.  split. simpl+. fsetdec'. assumption.
Qed.

Lemma codom_Sub_skvars_codom_Sub : forall τ θ,
    τ ∈τ codom_Sub θ
  -> fv__α(τ) ⊆ skvars_codom_Sub θ.
Proof.
  intros. ind_Sub θ. crush.
  simpl+ in H. destr_union.
  - simpl+. fsetdec.
  - specializes IHθ. crush.
    simpl+. fsetdec.
Qed.

Lemma bindings_Sub_sub_skvars_codom_Sub_sub : forall θ1 θ2,
    bindings_Sub θ1 ⊆τx bindings_Sub θ2
  -> skvars_codom_Sub θ1 ⊆ skvars_codom_Sub θ2.
Proof.
  introv SUB. unfolds in SUB. unfolds. intros.
  - forwards [α__index [τ [IN1 IN2]]]: skvars_codom_Sub_bindings_Sub. eassumption.
    specializes SUB IN1.
    forwards: bindings_Sub_dom_Sub1 θ2. eassumption.
    forwards: codom_Sub_skvars_codom_Sub τ θ2. eassumption.
    fsetdec.
Qed.


Lemma dom_codom_disj_Sub_bindings_Sub : forall θ1 θ2,
    dom_codom_disj_Sub θ2
  -> bindings_Sub_sub θ1 θ2
  -> dom_codom_disj_Sub θ1.
Proof.
  unfold dom_codom_disj_Sub. intros. unfolds in H0.
  eapply atoms_facts.disjoint_Subset. eassumption.
  auto using bindings_Sub_sub_dom_Sub_sub.
  auto using bindings_Sub_sub_skvars_codom_Sub_sub.
Qed.

#[export] Hint Resolve P_Sub_uni P_Sub_dom_codom : core.

Lemma P_Sub_bindings_Sub : forall θ1 θ2,
    P_Sub θ2
  -> bindings_Sub_sub θ1 θ2
  -> P_Sub θ1.
Proof.
  intros. split; eauto using uni_Sub_bindings_Sub, dom_codom_disj_Sub_bindings_Sub, dom_codom_disj_Sub_bindings_Sub.
Qed.

Lemma P_Sub'_bindings_Sub : forall θ1 θ2,
    P_Sub' θ2
  -> bindings_Sub_sub θ1 θ2
  -> P_Sub' θ1.
Admitted.
