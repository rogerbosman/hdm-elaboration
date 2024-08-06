Set Warnings "-notation-overridden,-intuition-auto-with-star".

Require Import Preamble.

Require Import Defs.ERels.
Require Import Defs.Subst.
Require Import Defs.WfE.
Require Import Defs.WfSTt.

Lemma E_lookup_some : forall ψ x σ,
    E_lookup ψ x = Some σ
  -> x ∈ E_names ψ
  /\ σ ∈σ E_schemes ψ.
Proof.
  intros. induction ψ; simpl+. 1,2,4:crush.
  simpl+ in H. if_dec. split. fsetdec. inverts H. fsetdec. crush.
Qed.
Corollary E_lookup_some1 : forall ψ x σ,
    E_lookup ψ x = Some σ
  -> x ∈ E_names ψ.
Proof. intros. apply E_lookup_some in H. jauto. Qed.
Corollary E_lookup_some2 : forall ψ x σ,
    E_lookup ψ x = Some σ
  -> σ ∈σ E_schemes ψ.
Proof. intros. apply E_lookup_some in H. jauto. Qed.
#[export] Hint Resolve E_lookup_some1 E_lookup_some2 : core.

Lemma E_lookup_some' : forall ψ x,
    x ∈ E_names ψ
  -> exists σ, E_lookup ψ x = Some σ.
Proof.
  intros. induction ψ. 1,2,4:crush. simpl. if_dec.
  - exists. reflexivity.
  - simpl+ in H. destr_union. eauto. crush.
Qed.

Fact E_lookup_nointinnames : forall ψ x,
    x ∉ E_names ψ
  -> E_lookup ψ x = None.
Proof. introv NIE. induction ψ. 1,2,4:crush. simpl+. if_dec. simpl+ in NIE. fsetdec. crush. Qed.
#[export] Hint Resolve E_lookup_nointinnames : core.

Lemma E_lookup_subst_name : forall x__in x__out ψ x σ,
    E_lookup ψ x = Some σ
  -> x__in ∉ E_names ψ
  -> E_lookup ({x__in ↤__x x__out}ψ) ({x__in ≔ x__out} x) = Some σ.
Proof.
  introv LU NIE. induction ψ; simpl+ in LU. 1,2,4:crush.
  if_dec.
  - inverts LU. simpl+. if_taut.
  - simpl+. if_dec. 2:apply IHψ; try eassumption; fsetdec+.
    unfold_subst_var in EQ. if_dec.
    + crush.
    + subst. false. apply NIE. fsetdec+.
    + forwards: E_lookup_some. eassumption. fsetdec+.
    + crush.
Qed.

(* Fact E_lookup_subst_skvar_binding_E : forall ψ α β x σ, *)
(*     E_lookup ψ x = Some σ *)
(*   -> E_lookup ({β ≔__α α}ψ) x = Some ({T__Var_f β ≔ α} σ). *)
(* Proof. intros. induction ψ. 1,2,4: crush. simpl+. simpl+ in H. if_dec. inverts H. crush. crush. Qed. *)

Fact E_lookup_distr : forall ψ2 ψ1 x σ,
    E_lookup (ψ1 +++ ψ2) x = Some σ
  -> E_lookup ψ2 x = Some σ
  \/ E_lookup ψ2 x = None
  /\ E_lookup ψ1 x = Some σ.
Proof.
  induction ψ2; introv IN; simpl+ in *. crush.
  - forwards: IHψ2. eassumption. destruct H; crush.
  - if_dec. crush.
    forwards: IHψ2. eassumption. destruct H; crush.
  - forwards: IHψ2. eassumption. destruct H; crush.
Qed.

Fact E_lookup_app__l : forall ψ2 ψ1 x σ,
    E_lookup ψ2 x = Some σ
  -> E_lookup (ψ1 +++ ψ2) x = Some σ.
Proof.
  intros. induction ψ2; simpl+. 1,2,4: crush.
  simpl+ in H. if_dec; crush.
Qed.
#[export] Hint Resolve E_lookup_app__l : elookup.

Fact E_lookup_none__r : forall ψ2 ψ1 x,
    E_lookup ψ2 x = None
  -> E_lookup (ψ1 +++ ψ2) x = E_lookup ψ1 x.
Proof.
  intros. induction ψ2; simpl+. 1,2,4: crush.
  simpl+ in H. if_dec; crush.
Qed.

Fact E_lookup_app__r : forall ψ2 ψ1 x σ,
    E_lookup ψ1 x = Some σ
  -> E_lookup ψ2 x = None
  -> E_lookup (ψ1 +++ ψ2) x = Some σ.
Proof.
  intros. rewrite E_lookup_none__r; crush.
Qed.
#[export] Hint Resolve E_lookup_app__r : elookup.

Fact E_lookup_wf : forall ψ x σ,
    E_lookup ψ x = Some σ
  -> wf(ψ)
  -> ψ ⊢wfσ σ.
Proof.
  introv LU WFE. induction ψ; simpl+ in LU; inverts LU; inverts WFE.
  - eapply WfS_E_A_sk_sub. eauto. unfolds. simpl+. fsetdec.
  - if_dec.
    + inverts H0.
      eapply WfS_E_A_sk_sub. eauto. unfolds. simpl+. fsetdec.
    + eapply WfS_E_A_sk_sub. eauto. unfolds. simpl+. fsetdec.
  - eapply WfS_E_A_sk_sub. eauto. unfolds. simpl+. fsetdec.
Qed.

Fact E_lookup_rename_skvar_E : forall α β ψ x σ,
    E_lookup ψ x = Some σ
  -> E_lookup ({β ↤ α}ψ) x = Some ({T__Var_f β ≔ α}σ).
Proof.
  introv LU. induction ψ; simpl+ in LU; inverts LU; simpl+. 1,3:crush.
  if_dec; crush.
Qed.

(*** Alg *)
Require Import Preamble.Tag.

Lemma E_lookup_alg_E : forall ψ x σ,
    E_lookup ψ x = Some σ
  -> alg_E ψ
  -> alg_L (fv__α(σ)).
Proof.
  introv IN ALG. induction ψ; simpl+ in *.
  - crush.
  - eapply IHψ. eassumption. eauto.
  - if_dec. inverts IN. eapply alg_L_subset. eassumption. reldec. eauto.
  - eapply IHψ. eassumption. eauto.
Qed.

(*** E_lookup/subst_name_E *)
Corollary subst_name_E_in__eq : forall σ ψ x__in x__out,
    E_lookup ψ x__out = Some σ
  -> x__in ∉ E_O_names ψ
  -> E_lookup ({x__in ↤__x x__out}ψ) x__in = Some σ.
Proof.
  introv LU NEQ. induction ψ. 1,2,4:crush.
  simpl+ in LU. if_dec.
  - inverts LU. simpl+. if_taut.
  - simpl+. unfold_subst_var. if_dec.
    + if_dec. crush. simpl+ in NEQ. subst. crush.
    + crush.
    + crush.
Qed.

Corollary subst_name_E_in__neq : forall x__lu x__out x__in σ ψ,
    E_lookup ψ x__lu = Some σ
  -> x__lu <> x__out
  -> x__lu <> x__in
  -> E_lookup ({x__in ↤__x x__out}ψ) x__lu = Some σ.
Proof.
  introv LU NEQ NEQ'. induction ψ. 1,2,4:crush.
  simpl+ in LU. if_dec.
  - inverts LU. simpl+. unfold_subst_var.
    if_dec. crush. crush. crush.
  - simpl+. unfold_subst_var.
    destruct (x == x__out).
    + if_dec. crush. crush.
    + if_dec; crush.
Qed.
