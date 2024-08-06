Set Warnings "-notation-overridden,-intuition-auto-with-star".

Require Import Preamble.
Require Import Preamble.Tag.
Require Import Defs.HdmLems.

Require Import Defs.ERels.
Require Import Defs.FrA.
Require Import Defs.Freevars.
Require Import Defs.Subst.
Require Import Defs.WfSTt.
(*** Notations *)
Notation  "L ⊢ t1 ▸ σ ≤ t2 ▸ ⟨ a ⟩ τ" := (Inst t1 σ t2 a τ L) (at level 50, only printing, format "L  ⊢  t1  ▸  σ  ≤  t2  ▸  ⟨ a ⟩  τ" ) : type_scope.

(*** Rewr *)
Lemma Inst_subset : forall L1 L2 t1 σ t2 a τ,
    Inst t1 σ t2 a τ L1
  -> L2 ⊆ L1
  -> Inst t1 σ t2 a τ L2.
Proof.
  introv INST SUB. gen L2. induction INST; intros. crush.
  econstructor. fsetdec. assumption. eapply IHINST. fsetdec.
Qed.
#[export] Hint Resolve Inst_subset : core.
#[export] Instance Inf_subset_proper : Proper (eq ==> eq ==> eq ==> eq ==> eq ==> flip Subset ==> impl) Inst.
  autounfold. intros. subst. eauto.
Qed.

(*** Alg *)
Lemma Inst_alg_A : forall t1 σ t2 a τ L,
    Inst t1 σ t2 a τ L
  -> alg_A a.
Proof.
  introv INST. induction INST. crush.
  eapply alg_A_cons; crush.
Qed.

Lemma Inst_alg_T : forall t1 σ t2 a τ L,
    Inst t1 σ t2 a τ L
  -> alg_L (fv__α(σ))
  -> alg_L (fv__α(τ)).
Proof.
  introv INST ALG. induction INST. crush.
  eapply IHINST. rewrite fsk_Sc_open_Sc_wrt_T_upper.
  eapply alg_L_union. simpl+. eassumption. crush.
Qed.

Lemma Inst_alg_Tm : forall t1 σ t2 a τ L,
    Inst t1 σ t2 a τ L
  -> alg_L (fv__α(t1))
  -> alg_L (fv__α(t2)).
Proof.
  introv INST ALG. induction INST. crush.
  eapply IHINST. simpl+. eapply alg_L_union; crush.
Qed.

(*** Unsorted *)
Lemma Inst_free_skvars : forall t1 σ t2 a τ L,
    Inst t1 σ t2 a τ L
  -> fv__α(σ) ⊆ fv__α(τ).
Proof.
  introv INST. induction INST. crush. simpl+.
  rewrite fsk_Sc_open_Sc_wrt_T_lower. eassumption.
Qed.

Lemma Inst_names : forall t1 σ t2 a τ L,
    Inst t1 σ t2 a τ L
  -> fv__x(t1) = fv__x(t2).
Proof. introv INST. induction INST; crush. Qed.

Lemma Inst_WfT : forall t1 σ1 t2 a τ2 L ψ,
    Inst t1 σ1 t2 a τ2 L
  -> ψ ⊢wfσ σ1
  -> ψ ⊢wft t1
  -> (ψ ::a a) ⊢wfτ τ2
  /\ (ψ ::a a) ⊢wft t2.
Proof.
  introv INST WfS Wft. gen ψ. induction INST; intros.
  - split.
    eapply WfT_E_A_sk_sub. eauto. reldec.
    eapply Wft_E_A_sk_sub. eauto. reldec. reldec.
  - specializes IHINST. applys WfS_open_Sc_wrt_T' WfS.
    eapply Wft_tapp. split.
    eapply Wft_E_A_sk_sub. eauto. reldec. reldec. apply WfT_var. reldec.
    destr. split.
    eapply WfT_E_A_sk_sub. eauto. reldec.
    eapply Wft_E_A_sk_sub. eauto. reldec. reldec.
Qed.

Lemma Inst_FrA : forall t1 σ1 t2 a τ2 L,
    Inst t1 σ1 t2 a τ2 L
  -> a ### L.
Proof. introv INST. induction INST. crush. eapply FrA_shift'. eassumption. fsetdec. Qed.

Lemma Inst_subst_name : forall x__in x__out L t1 σ t2 a τ,
    Inst t1 σ t2 a τ L
  -> Inst ({t__Var_f x__in ≔__x x__out}t1) σ ({t__Var_f x__in ≔__x x__out}t2) a τ L.
Proof. introv INST. induction INST; crush. Qed.

Fact Inst_ftv_sub : forall t1 σ t2 a τ L,
    Inst t1 σ t2 a τ L
  -> fv__x(t2) = fv__x(t1).
Proof.
  introv INST. induction INST; crush.
Qed.

Corollary Inst_ftv_sub__neq : forall x__in x__out x σ t a τ L,
    Inst (t__Var_f x) σ t a τ L
  -> x <> x__out
  -> Inst (t__Var_f x) σ ({t__Var_f x__in ≔__x x__out}t) a τ L.
Proof.
  introv INST NEQ. applys_eq INST. apply subst_tvar_Tm_notin.
  erewrite Inst_ftv_sub. 2:eassumption. crush.
Qed.
